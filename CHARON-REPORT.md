# Charon extraction: Binder deserializer

Charon is the Rust front-end of the Aeneas toolchain. This stage extracts the
parsing code of the Linux kernel's Rust Binder driver into LLBC, and measures
what stands between kernel Rust and extraction.

Charon extracts the BinderObject deserializer with zero changes to the parsing
logic. Unions, `MaybeUninit`, raw-pointer casts, `unsafe`,
`unreachable_unchecked`, closures, and `?` all pass. The only work is replacing
the kernel environment (kernel crate, bindgen'd UAPI, the userspace reader) with
a thin stub layer.

This report describes the original extraction (Charon v0.1.219). The repo has
since moved to v0.1.220, Aeneas's pinned version, with `--preset=aeneas`; see
[AENEAS-REPORT.md](AENEAS-REPORT.md) for the next stage.

## What was extracted

The `BinderObject` deserializer from `drivers/android/binder/allocation.rs`
(v7.2-rc2, lines 452-565): `read_from`, `read_from_inner`, `as_ref`, `size`,
`type_to_size`, the `BinderObjectRef` view enum, plus the pure validators
`ptr_align`, `is_aligned`, and `size_check`. This is the "parse untrusted
bytes → validate tag → typed decode" surface: it reads a userspace buffer,
rejects unknown type tags with EINVAL, and produces a size-checked typed view.
It also concentrates the hard features (union type-punning, `MaybeUninit` +
`assume_init`, a raw-pointer cast) that determine feasibility.

The heavier `copy_transaction_data` loop and `translate_object` were excluded.
They pull in `Process`, `Node`, refcounting, security contexts, and dozens of C
`bindings` calls, a stub surface too large for a spike.

## Stubs

Parsing bodies are byte-for-byte identical to the kernel source; every deviation
is marked `// SPIKE-STUB: <reason>` in [src/lib.rs](src/lib.rs). Summary: local
`Error`/`EINVAL` instead of `kernel::error`; empty `FromBytes`/`AsBytes` markers;
hand-written `#[repr(C)]` copies of the five UAPI structs (layouts verified
against the C header); `SliceReader` over `&[u8]` with the same 4-method surface
as `UserSliceReader`; `size_check` as a free function; a `parse_one` entry point
with tests. No parsing arithmetic or control flow was changed. `cargo test`: 3/3.

## Charon outcome

`charon cargo`: exit 0, no warnings, `spike_binder.llbc` produced.
Pretty-printing confirms the extraction is faithful: the union type-punning
survives (`as_ref` lowers to a switch on the tag with raw union field reads), the
`MaybeUninit`/pointer-cast chain in `read_from_inner` is explicit
(`cast<BinderObject, [u8; 40]>`), `?` and the closure desugar normally.

## Barriers between kernel Rust and Charon

The barriers are environmental, in descending order of cost:

1. The `kernel` crate. Everything non-trivial routes through it (`Arc`, `KVec`,
   locks, `pin_data`, `UserSlice`, security, and more). For a parsing leaf the
   stub is small; for `copy_transaction_data` it explodes. Modelling kernel APIs,
   rather than passing Charon, is the dominant cost.
2. bindgen'd UAPI/`bindings`. Real kernel Rust gets these generated from C
   headers at build time; layout fidelity matters because the code relies on
   `size_of` and union punning.
3. FFI boundaries. Calls into C have no Rust body; they extract as opaque. Fine
   for pure parsers, blocking for the side-effecting paths.
4. Toolchain skew. The kernel wants its blessed nightly with `#![feature(...)]`;
   Charon pins its own. Our fragment needed none of them.
5. Verification side. The union/`assume_init` invariants live in SAFETY comments,
   not types; proving them is where the cost reappears downstream. Confirmed:
   Aeneas rejects the unions outright; see [AENEAS-REPORT.md](AENEAS-REPORT.md)
   and upstream issue
   [AeneasVerif/aeneas#1199](https://github.com/AeneasVerif/aeneas/issues/1199).

Self-contained parsing leaves are close to Charon-acceptable; the gap is a
mechanical stub layer. The distance grows with dependency depth.

## Next candidates (not yet extracted)

From a sweep of `drivers/**/*.rs`, best first:

| Candidate | File | Why |
|---|---|---|
| MCTP/NVDM headers | `drivers/gpu/nova-core/mctp.rs` (88 L, 0 unsafe) | validate untrusted firmware-message headers; smallest next target |
| VBIOS parser | `drivers/gpu/nova-core/vbios.rs` (1004 L, 8 unsafe) | parse a hostile BIOS blob; the substantive target |
| GSP command queue | `drivers/gpu/nova-core/gsp/cmdq.rs` (849 L, 5 unsafe) | parse firmware RPC responses from a DMA ring |
| sbuffer | `drivers/gpu/nova-core/sbuffer.rs` (224 L, 0 unsafe) | byte-cursor primitive the GSP parsers build on |

## Environment

Kernel v7.2-rc2 (tree not modified), Charon v0.1.219 (commit `19e3f85a`,
toolchain `nightly-2026-06-01`), crate on stable rustc/cargo 1.94.0. See
[README.md](README.md) for current reproduce steps with v0.1.220.
