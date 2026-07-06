# Feasibility Spike: Extracting Kernel Rust (Binder) with Charon

**Goal.** Measure the distance between the Linux kernel's Rust Binder driver and
what Charon (the Rust→LLBC front-end of the Aeneas verification toolchain)
accepts, by extracting a real parsing fragment into a standalone crate and
running Charon on it.

**Pipeline.** Rust → Charon → (Aeneas → Lean 4). This spike only exercises the
**Rust → Charon → LLBC** step.

**Environment.**
- Kernel tree: `~/linux` at **v7.2-rc2** (`git describe` = `v7.2-rc2`). Not modified.
- Toolchain (crate): `rustc 1.94.0` stable, `cargo 1.94.0`.
- Charon: built from source (`github.com/AeneasVerif/charon`), **version 0.1.219**,
  commit **`19e3f85a32e02ef00664fa325bbbf157678be530`**, pinned toolchain
  `nightly-2026-06-01` (rustc 1.98.0-nightly). Built via `make build-charon-rust`;
  binaries in `~/charon/bin/{charon,charon-driver}`.
- Spike crate: `spike_binder` (this repository).

---

## (a) What Binder parsing code exists, and where

All paths are under `drivers/android/binder/` unless noted. The Rust Binder
driver is ~9,500 lines across 19 files. The code that parses/validates data
arriving **from userspace** (via the `binder_write_read` ioctl transaction path)
is concentrated in four places:

### 1. `defs.rs` (182 lines) — UAPI struct wrappers
- Lines 86–144: `decl_wrapper!` macro + declarations wrapping the bindgen'd C
  UAPI structs (`FlatBinderObject`, `BinderTransactionData`, `BinderObjectHeader`,
  `BinderBufferObject`, `BinderFdObject`, `BinderFdArrayObject`, …). Each is a
  `#[repr(transparent)]` newtype over `MaybeUninit<uapi::…>` with `unsafe impl
  FromBytes`/`AsBytes`, so raw userspace bytes can be reinterpreted as the struct
  while preserving padding.
- Lines 18–79: `BC_*`/`BR_*`/flag constants pulled from `kernel::uapi`.
- **Deps:** `kernel::transmute::{AsBytes,FromBytes}`, `kernel::uapi`,
  `kernel::macros::concat_idents`, `core::mem::MaybeUninit`.

### 2. `allocation.rs` (611 lines) — object (de)serialization + bounds checks ★
- **`BinderObject` union + impls, lines 452–565** — the core deserializer of a
  single flattened binder object read from the userspace buffer:
  - `read_from` (477) / `read_from_inner` (503): zero a `MaybeUninit<BinderObject>`,
    fill it from a reader via a raw-pointer cast to `&mut [u8; N]`, read the type
    tag, **reject unknown types with `EINVAL`**, then `assume_init`.
  - `as_ref` (527): match on the type tag and return a typed view into the union
    (`BinderObjectRef`), with `unreachable_unchecked` on the impossible arm.
  - `size` (545) / `type_to_size` (553): map the type tag to the object size.
- **`Allocation::size_check`, lines 82–89** — the offset/length overflow +
  bounds validator (`checked_add` for overflow, `wrapping_add > self.size` for
  bounds). Used by every `read`/`write`/`copy_into` into an allocation.
- **`AllocationView::{read,write,copy_into}`, lines 342–366** — a second bounds
  check against a `limit` before delegating to `Allocation`.
- `cleanup_object` (422) / `transfer_binder_object` (368): interpret parsed
  objects; heavier kernel deps (nodes, handles, refcounts).
- **Deps:** `kernel::uaccess::UserSliceReader`, `kernel::uapi`,
  `kernel::transmute`, `kernel::prelude` (`Result`/`EINVAL`), plus (for the
  non-parsing methods) `kernel::fs::file`, `sync::Arc`, `KVec`, and C `bindings`.

### 3. `thread.rs` (1661 lines) — the transaction-copy driver loop
- **`copy_transaction_data`, lines 952–1080+** — the top-level routine that reads
  a transaction from userspace: validates `offsets_size`/`buffers_size` alignment
  (`is_aligned`, 983–988), computes the total allocation size with checked
  arithmetic (991–998), then **loops over the offset array** (1035–1078): reads
  each `u64` offset, checks it is monotonic and `u32`-aligned (1043), copies
  inter-object data, and calls `BinderObject::read_from` (1057) + `translate_object`.
- `translate_object` (655) + `is_aligned` (39).
- **Deps:** heavy — `UserSlice`, `Process`, `Node`, `ScatterGatherState`,
  `security::SecurityCtx`, `KVec`, C `bindings`, plus everything in (2).

### 4. `include/uapi/linux/android/binder.h` — the C struct layouts
- `binder_object_header` (66), `flat_binder_object` (77), `binder_fd_object` (99),
  `binder_buffer_object` (129), `binder_fd_array_object` (163); `BINDER_TYPE_*`
  (32–38, computed via `B_PACK_CHARS`).

---

## (b) Fragment chosen, and why

**Chosen:** the **`BinderObject` deserializer** from `allocation.rs:452–565`
(`read_from`, `read_from_inner`, `as_ref`, `size`, `type_to_size`, and the
`BinderObjectRef` view enum), plus the pure validators `ptr_align`
(`rust_binder_main.rs:283`), `is_aligned` (`thread.rs:39`), and the arithmetic of
`Allocation::size_check` (`allocation.rs:82`).

**Why this one:**
1. **It is genuinely "parse untrusted bytes → validate → typed decode."** It
   takes an opaque byte buffer coming from userspace, reads a type tag, rejects
   invalid tags (`EINVAL`), and produces a typed, size-checked view — exactly the
   deserialization surface the spike targets.
2. **Smallest self-contained unit with few kernel deps.** Its only real external
   dependencies are (i) the `uapi` `#[repr(C)]` structs (plain data, trivially
   stubbable) and (ii) a byte reader (`UserSliceReader`) whose method surface used
   here is tiny: `len`, `clone_reader`, `read_slice`, `skip`. Everything else
   (`Arc`, `KVec`, `Node`, `Process`, `bindings`, allocators) lives in the
   *translate/cleanup* half of the file, which we deliberately excluded.
3. **It concentrates the hard Rust features** that determine Charon feasibility:
   `union` type-punning, `MaybeUninit` + `zeroed` + `assume_init`, a
   raw-pointer cast (`*mut T` → `*mut [u8; N]`), `unsafe` blocks,
   `core::hint::unreachable_unchecked`, an `FnOnce` closure bound, and the `?`
   operator. If Charon handles this fragment, it handles the representative core.
4. `size_check`/`ptr_align`/`is_aligned` are added as the pure offset/length
   validators the prompt calls out — trivial arithmetic, byte-for-byte.

The heavier `copy_transaction_data` loop and `translate_object` were **not**
chosen: they transitively pull in `Process`, `Node`, refcounting, security
contexts, DMA/scatter-gather state, and dozens of C `bindings` calls — a stub
surface far too large for a feasibility spike, and dominated by side-effecting
kernel calls rather than parsing logic.

---

## (c) Full list of stubs / modifications

The crate is `~/spike-binder/` (`Cargo.toml` + `src/lib.rs`). The parsing bodies
of `read_from`, `read_from_inner`, `as_ref`, `size`, `type_to_size`, `ptr_align`,
`is_aligned` are **byte-for-byte identical** to the kernel source. Every
deviation is marked `// SPIKE-STUB: <reason>` in the source. Summary:

| # | Stub / change | Replaces | Reason |
|---|---------------|----------|--------|
| 1 | `#![no_std]` + `kernel` crate dropped; ordinary std crate | kernel environment | build with stable cargo |
| 2 | `struct Error(i32)`, `const EINVAL/ENOMEM`, `type Result<T>` | `kernel::error::{Error,Result}`, `EINVAL` | only errno identity is needed by the parser |
| 3 | `unsafe trait FromBytes {}` / `AsBytes {}` (empty markers) | `kernel::transmute::{FromBytes,AsBytes}` | same marker semantics, local definition |
| 4 | `mod uapi { … }` — hand-written `#[repr(C)]` copies of the 5 binder structs (+ anon unions) | bindgen'd `kernel::uapi::*` | reproduce identical layout on 64-bit (`binder_uintptr_t=binder_size_t=u64`) |
| 5 | `BINDER_TYPE_*` inlined as `u32` literals | `kernel::uapi::BINDER_TYPE_*` | values computed from `B_PACK_CHARS`/`B_TYPE_LARGE`, verified against the C header |
| 6 | `struct SliceReader<'a>` over `&[u8]` with `len`/`clone_reader`/`read_slice`/`skip` | `kernel::uaccess::UserSliceReader` | in-memory byte source instead of `copy_from_user`; identical method surface, so `read_from` is unchanged |
| 7 | `pub(crate)` → `pub` on the extracted items | — | crate has no parent module |
| 8 | `size_check` made a free fn taking `buffer_size` explicitly | `Allocation::size_check` method (`self.size`) | detach from the `Allocation` struct; arithmetic unchanged |
| 9 | `pub fn parse_one(&[u8])` driver + `#[cfg(test)]` tests | — (not in kernel) | provide a top-level entry point and sanity checks |

No change was made to any *parsing arithmetic or control flow*. The crate builds
clean on stable (`cargo build`, `cargo test` → 3/3 pass).

---

## (d) Charon results, per iteration

Command (run in `~/spike-binder/`): `charon cargo`

### Iteration 1 — **SUCCESS on first attempt**

```
   Compiling spike_binder v0.1.0 (/home/natalie/spike-binder)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 13.52s
```

- Exit code: **0**
- Warnings: **0**. Errors: **0**. (`grep -icE 'warning|error'` over the log = 0.)
- Output: **`spike_binder.llbc` (801,363 bytes)** produced.

No iterations 2 or 3 were needed — there were no failures to categorize or fix.

**Verification that the extraction is real (not empty).** Pretty-printing the
LLBC (`charon pretty-print spike_binder.llbc`, 2,223 lines) shows every target
function present with faithful semantics:

- `type_to_size`, `read_from_inner`, `read_from`, `as_ref`, `size`, `ptr_align`,
  `is_aligned`, `size_check`, `parse_one` all extracted.
- **Union type-punning preserved** — `as_ref` lowers to a `switch` on
  `(((*self)).hdr).type_` with arms building `&mut ((*self)).fbo`,
  `… .fdo`, `… .bbo`, `… .fdao` — i.e. the raw union field reads survive:
  ```
  switch copy (((*self)).hdr).type_ {
      2002922117u32 | 1935813253u32 => { … },      // BINDER / WEAK_BINDER
      1717840517u32 => { _7 = &mut ((*self)).fdo; _0 = BinderObjectRef::Fd {..} },
      …
  }
  ```
- **Raw-pointer cast + `MaybeUninit` preserved** — `read_from_inner` lowers the
  `obj.as_mut_ptr().cast()` chain explicitly:
  ```
  obj = zeroed<BinderObject>()
  _11 = as_mut_ptr<BinderObject>(move _12)
  _10 = cast<BinderObject, [u8; 40usize]>(move _11)
  ```
  (`[u8; 40]` == `size_of::<BinderObject>()`, the largest variant
  `binder_buffer_object`.)
- **`?` operator** desugared to `impl_Try_for_Result::branch` / `ControlFlow`;
  **`FnOnce` closure** lowered to `TraitClause1::call_once`; SAFETY comments
  carried through into the LLBC dump.

**Assessment of this result:** Charon accepted the representative unsafe/union/
raw-pointer core of the Binder deserializer with **zero** source changes to the
parsing logic — the only work was replacing the *ambient kernel environment*
(std vs no_std, error type, byte reader, UAPI struct source) with equivalent
stubs. That is a strongly positive feasibility signal for the Rust→Charon step.

---

## (e) Main technical barriers between kernel Rust and Charon extraction

The spike shows the barrier is **not** the parsing language features. Charon
0.1.219 handled unions, `MaybeUninit`, raw-pointer casts, `unsafe`,
`unreachable_unchecked`, closures, and `?` out of the box. The real distance is
the **environment and dependency surface**, in roughly descending order of cost:

1. **The `kernel` crate is the whole iceberg.** Kernel Rust is `#![no_std]` and
   everything non-trivial routes through `kernel::` — `Arc`/`ARef`, `KVec` and
   fallible allocation (`GFP_KERNEL`, `AllocError`), `SpinLock`/`Mutex`,
   `pin_data`/`#[pin]`, `UserSlice(Reader)`, `security`, `task`, `time`, tracing.
   For the *parsing leaf* we stubbed a 4-method reader and 5 structs; for
   `copy_transaction_data` the stub surface explodes. **The dominant cost is
   modelling `kernel` crate APIs, not getting Rust past Charon.** Whether these
   are stubbed (as here) or extracted for real (Charon would have to ingest the
   `kernel` crate + its C `bindings`) is the central open question.

2. **bindgen'd C UAPI / `bindings`.** Real kernel Rust gets `uapi::*` and
   `bindings::*` from bindgen over C headers. Charon runs as a rustc driver, so
   in principle it can consume the generated Rust — but that requires the kernel
   build system to produce those bindings first (the spike sidesteps this by
   hand-writing `#[repr(C)]` equivalents). Layout/`repr` fidelity matters because
   the code relies on `size_of` and union punning.

3. **FFI / `extern "C"` boundaries.** Calls into C (`bindings::…`) have no Rust
   body for Charon to translate; they become opaque. Any function that actually
   touches C (allocator, file table, security, DMA) will extract only as an
   uninterpreted call — fine for a purely-Rust parser, blocking for the
   side-effecting translate/copy path.

4. **Unstable `#![feature(...)]` and toolchain skew.** `rust/kernel/lib.rs`
   enables nightly features (e.g. `generic_arg_infer`) and tracks a specific
   kernel-blessed rustc. Charon pins its **own** nightly (`2026-06-01` here). A
   real extraction must reconcile the kernel's required toolchain/features with
   Charon's pinned one; our fragment happened to need none of them, so stable
   sufficed.

5. **Verification-side (downstream of Charon, not tested here).** Even once LLBC
   is produced, Aeneas/Lean must cope with the parts Charon extracts *verbatim*:
   the union-based type-punning and `assume_init` reads encode invariants ("all
   bytes initialized; `hdr.type_` is a valid tag") that live in SAFETY comments,
   not types. Charon emits them faithfully, but proving them in Lean is where the
   `unsafe`/union modelling cost reappears.

**Bottom line.** For self-contained parsing/validation leaves, kernel Rust is
**close** to Charon-acceptable — the gap is a mechanical stub layer for the
`kernel` crate and UAPI bindings, not unsupported language constructs. The
distance grows with dependency depth: anything transitively needing allocation,
locking, FFI, or `pin`-init requires either faithful extraction of the `kernel`
crate or a much larger stub effort.

---

## Step 6 — Second-round candidates (untrusted/external-input parsers)

Found by sweeping `drivers/**/*.rs` and `rust/`. Listed most-promising-first
(smaller / fewer kernel deps / clearer parse-untrusted-bytes shape). **Not yet
extracted.**

| Candidate | File | One-line description |
|-----------|------|----------------------|
| **MCTP/NVDM headers** | `drivers/gpu/nova-core/mctp.rs` (88 L, **0 unsafe**) | Decode/validate MCTP transport + NVIDIA vendor-message headers from GSP firmware traffic: `NvdmType::try_from(u8)`, `MctpHeader`/`NvdmHeader` bitfield parse + `validate()`. Smallest, cleanest next target. |
| **VBIOS parser** | `drivers/gpu/nova-core/vbios.rs` (1004 L, 8 unsafe) | Parse an untrusted BIOS image pulled off the card: PCIR/BIT/`BiosImage` tables, offset/size walking over `&[u8]` (`from_id`, per-image `new(data:&[u8])`). The richest real "parse hostile blob" target. |
| **GSP command queue** | `drivers/gpu/nova-core/gsp/cmdq.rs` (849 L, 5 unsafe) | Read/validate GSP RPC responses out of a shared DMA ring buffer — the closest analogue to "parse responses from firmware." |
| **FWSEC firmware** | `drivers/gpu/nova-core/firmware/fwsec.rs` (416 L, 11 unsafe) | Parse & fix up FWSEC firmware headers extracted from the VBIOS before authentication. |
| **GSP FW commands** | `drivers/gpu/nova-core/gsp/fw/commands.rs` + `fw.rs` | Typed layouts of GSP firmware command/response structs (`FromBytes`-style), consumed by `cmdq`. |
| **sbuffer** | `drivers/gpu/nova-core/sbuffer.rs` (224 L, 0 unsafe) | Discontiguous byte-slice cursor abstraction (the reader primitive the GSP parsers build on) — a good pure-logic warm-up. |
| **DRM panic QR** | `drivers/gpu/drm/drm_panic_qr.rs` (1016 L, 6 unsafe) | QR *encoder* (no-alloc). Not untrusted-input parsing, but a large self-contained bit-manipulation Rust unit useful as a Charon stress test. |
| **rnull configfs** | `drivers/block/rnull/configfs.rs` | Parse configfs attribute values (user-supplied strings → typed config). |

**Recommendation for a second extraction:** `mctp.rs` for a quick second data
point (tiny, no unsafe, clear validate-untrusted-header shape), then `vbios.rs`
as the substantive "parse a hostile external blob" target.
