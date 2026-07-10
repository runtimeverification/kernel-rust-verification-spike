# Aeneas → Lean 4: Binder deserializer

**Goal.** Run Aeneas on the extracted Binder deserializer
(`drivers/android/binder/allocation.rs`, v7.2-rc2) targeting Lean 4, and assess
the distance to the maintainer's no-panic property: for all inputs from
userspace, the code must not panic.

**Result.** Aeneas does not support `union` types, and the deserializer is built
on union type-punning. Translation aborts on the union declarations; every
function that transitively touches the union (`read_from`, `read_from_inner`,
`as_ref`, `size`, `parse_one`) gets no Lean at all. The union-free validators do
translate, and no-panic is proved for three of them.

Upstream issue: https://github.com/AeneasVerif/aeneas/issues/1199

## The union failure

```
$ aeneas -backend lean llbc/spike_binder-charon-909ff09a-v0.1.220.llbc
[Error] unions are not supported   (flat_binder_object__bindgen_ty_1)
[Error] unions are not supported   (binder_fd_object__bindgen_ty_1)
[Error] unions are not supported   (BinderObject)
[Error] Internal error: ...        (cascade over all union-touching decls)
```

Exit code 2, no `.lean` produced. The rejection is a hard `craise` in
`TypesAnalysis.ml` with no CLI escape hatch (no `-opaque`/`-exclude` for types).

## Reduced union-free crate

To exercise the rest of the chain, [reduced/](reduced/) contains only the
union-free functions (`type_to_size`, `ptr_align`, `is_aligned`, `size_check`),
byte-for-byte where possible. Anonymous `union { u64; u32 }` fields are replaced
by `u64`; on a 64-bit target sizes are unchanged (asserted by a unit test).

This translates cleanly. The generated code is in
[lean/SpikeBinderReduced.lean](lean/SpikeBinderReduced.lean); a Lake project in
[lean/](lean/) typechecks it against the Aeneas stdlib (Lean/mathlib v4.31.0).

## Panic model

Aeneas puts every function in its `Result` monad: `ok v | fail e | div`. A panic
(overflow, division by zero, `unwrap` on `None`, `unreachable_unchecked`) is
exactly `fail`. No-panic is `∀ inputs, ∃ v, f inputs = ok v`. This is orthogonal
to the Rust-level `Result`: a clean EINVAL rejection is `ok (Err EINVAL)`, still
`ok` at the panic level — so "reject invalid input" and "never panic" are
properly distinguished.

## No-panic theorems ([lean/NoPanic.lean](lean/NoPanic.lean))

| Theorem | Status |
|---|---|
| `size_check_no_panic` | **Proved**, unconditional |
| `is_aligned_no_panic` (`to ≠ 0`) | **Proved**; companion proves it genuinely panics on `to = 0`, so the precondition is necessary (in the kernel, callers always pass nonzero constants) |
| `type_to_size_no_panic` | **Proved** modulo one axiom: `core.mem.size_of` is emitted as an opaque fallible axiom, not a concrete constant |
| `ptr_align_no_panic` | `sorry` — reachable, needs a manual model of the `Try` trait for `Option`; hours, not a blocker |
| `parse_one_no_panic` | **Cannot be stated** — `parse_one` has no Lean definition |

Proved theorems verified `sorry`-free via `#print axioms`.

## Distance to no-panic on `parse_one`

Blocked, not hard: the parsing core has no Lean representation, so no proof
effort closes the gap. Three ways forward:

1. **Upstream union support in Aeneas** (issue #1199) — the clean fix; nontrivial,
   unions interact with the borrow/region model.
2. **Union-free re-modelling** — `BinderObject` as `[u8; 40]` plus typed
   accessors, with the type-pun invariants ("all bytes initialized, tag valid")
   proved as explicit Lean propositions. Honest cost: the SAFETY-comment
   invariants become manual proof obligations. This is our current plan.
3. **Axiomatizing** the union functions as opaque Lean — fastest to green, but
   assumes away exactly the places (`unreachable_unchecked`, `assume_init`) where
   a panic would hide. Not acceptable for a security property.

## Reproduce

```sh
# Charon v0.1.220 (commit 909ff09a, Aeneas's pinned version), Aeneas c2015b86
charon cargo --preset=aeneas                     # full crate -> llbc
aeneas -backend lean llbc/spike_binder-charon-909ff09a-v0.1.220.llbc   # fails: unions

cd reduced && charon cargo --preset=aeneas       # union-free crate
aeneas -backend lean llbc/spike_binder_reduced-charon-909ff09a-v0.1.220.llbc -dest lean/

cd ~/aeneas-project/aeneas/backends/lean && lake exe cache get && lake build Aeneas
cd <repo>/lean && lake build
```

Environment: Aeneas `c2015b86`, Charon `909ff09a` (v0.1.220), Lean/mathlib
`v4.31.0`, stable rustc 1.94.0. Note: Aeneas requires `--preset=aeneas` at
Charon extraction time.