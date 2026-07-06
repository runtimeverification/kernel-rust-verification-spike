# Kernel Rust verification spike: Binder → Charon → LLBC

Can parsing code from the Linux kernel's Rust Binder driver be extracted,
unmodified, into LLBC — the input language of the Aeneas verification
toolchain (Rust → Lean 4)?

**Result: yes, on the first attempt.** The BinderObject deserializer
(drivers/android/binder/allocation.rs, v7.2-rc2) — including union
type-punning, MaybeUninit, a raw-pointer cast, and unsafe blocks — was
extracted by Charon with zero changes to the parsing logic. Only the
ambient kernel environment (the `kernel` crate, bindgen'd UAPI, the
userspace reader) was replaced with a thin stub layer, marked
`// SPIKE-STUB` in the source.

## Why

Binder parses untrusted bytes from arbitrary userspace apps. We want to
prove, in Lean 4 with kernel-checked proofs, that this parsing is correct:
bounds checks, tag validation, canonicity. This spike measures the first
step: the distance between kernel Rust and the verification toolchain.

## Reproduce

Verified with `rustc`/`cargo` 1.94.0 (stable) on Linux x86-64. The
`charon cargo` step produced `llbc/spike_binder.llbc` (checked into this
repo) with exit 0, zero warnings, zero errors.

```sh
# 1. Reference the kernel source the parsing logic was copied from (v7.2-rc2).
#    Only needed to diff against the original; the crate itself is self-contained.
git clone --depth 1 --branch v7.2-rc2 \
    https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git ~/linux

# 2. Build Charon from the exact commit used for this spike.
#    Its pinned toolchain (rust-toolchain: nightly-2026-06-01 + rustc-dev) is
#    fetched automatically by rustup during the build.
git clone https://github.com/AeneasVerif/charon.git ~/charon
cd ~/charon
git checkout 19e3f85a32e02ef00664fa325bbbf157678be530
make build-charon-rust          # produces ~/charon/bin/{charon,charon-driver}
~/charon/bin/charon version     # -> 0.1.219

# 3. Build the crate and extract it to LLBC.
cd <this-repo>
cargo build                     # stable toolchain; builds clean
cargo test                      # 3/3 tests pass
PATH="$HOME/charon/bin:$PATH" charon cargo   # -> spike_binder.llbc

# 4. (Optional) Pretty-print the extracted LLBC.
~/charon/bin/charon pretty-print spike_binder.llbc | less
```

- **Kernel:** v7.2-rc2
- **Charon:** v0.1.219, commit `19e3f85a32e02ef00664fa325bbbf157678be530`
  (pinned toolchain `nightly-2026-06-01`)
- **Crate toolchain:** stable `rustc`/`cargo` 1.94.0

## What's next

- Aeneas → Lean 4 on the extracted LLBC; first proofs of tag-rejection
  and bounds-check properties
- Second target: nova-core MCTP/VBIOS parsers
- The real prize: the offset-validation loop in copy_transaction_data
  (larger stub surface — see REPORT.md, section e)

## Who

Runtime Verification, Inc. Questions and comments welcome — via issues
or the Zulip thread (link TBA).
