# Kernel Rust verification spike: Binder → Lean 4

Can the Linux kernel's Rust Binder driver be verified post hoc, through the
Charon/Aeneas toolchain (Rust → LLBC → Lean 4)? Target property, from the
Binder maintainer: for all inputs from userspace, the code must not panic.

**Status.**
- Charon extracts the BinderObject deserializer
  (drivers/android/binder/allocation.rs, v7.2-rc2) with zero changes to the
  parsing logic. Only the kernel environment (kernel crate, bindgen'd UAPI,
  userspace reader) is stubbed, marked `// SPIKE-STUB` in the source.
  Details: [CHARON-REPORT.md](CHARON-REPORT.md).
- Aeneas rejects the union type-punning at the core of the deserializer, so
  the parsing functions get no Lean at all. Upstream issue:
  https://github.com/AeneasVerif/aeneas/issues/1199
- The union-free validators translate, and no-panic is proved for three of
  them (`size_check` unconditionally). Theorems: [lean/NoPanic.lean](lean/NoPanic.lean).
  Details: [AENEAS-REPORT.md](AENEAS-REPORT.md).
- A union-free re-modelling (`[u8; 40]` + typed accessors, per
  [AeneasVerif/aeneas#1199](https://github.com/AeneasVerif/aeneas/issues/1199))
  makes the **whole** deserializer translate to Lean. No-panic is proved for the
  accessors, reader primitives, `size`, and validators; `parse_one` is reduced
  to one mechanical goal over concrete, fail-free control flow.
  Theorems: [lean/NoPanicRemodel.lean](lean/NoPanicRemodel.lean).
  Details: [REMODEL-REPORT.md](REMODEL-REPORT.md).

## Layout

- `src/` — the extracted crate, parsing logic byte-for-byte from the kernel
- `reduced/` — union-free subset (validators only) that Aeneas accepts
- `remodel/` — union-free re-modelling of the full deserializer (`[u8; 40]` + accessors)
- `lean/` — generated Lean 4 code + no-panic theorems (Lake project)
- `llbc/` — Charon artifacts
- `CHARON-REPORT.md`, `AENEAS-REPORT.md`, `REMODEL-REPORT.md` — results per stage

## Reproduce

```sh
# Charon at commit 909ff09a (v0.1.220, the version Aeneas pins), Aeneas c2015b86
git clone https://github.com/AeneasVerif/charon.git ~/charon
cd ~/charon && git checkout 909ff09a && make build-charon-rust

cargo test                                        # 3/3
charon cargo --preset=aeneas                      # full crate -> llbc; Aeneas then fails on unions
cd reduced && charon cargo --preset=aeneas        # union-free crate -> translates
aeneas -backend lean llbc/spike_binder_reduced-charon-909ff09a-v0.1.220.llbc -dest lean/
cd lean && lake build                             # typechecks generated code + theorems
```

Kernel v7.2-rc2, Lean/mathlib v4.31.0, stable rustc 1.94.0. Aeneas requires
`--preset=aeneas` at extraction time.

## Next

- Close the final mechanical step in `parse_one_no_panic` (a `step`/reduction
  gap on tuple-pattern monadic binds — see REMODEL-REPORT.md §6)
- Upstream union support in Aeneas (issue #1199) — the faithful alternative to
  re-modelling
- Coverage map: the rest of the kernel's Rust through both pipeline stages

## Who

Runtime Verification, Inc. Issues welcome, or the
[Rust-for-Linux Zulip thread](https://rust-for-linux.zulipchat.com/#narrow/channel/288089-General/topic/Verifying.20Binder.27s.20parsing.20of.20userspace.20input.20in.20Lean.204/with/608640073).