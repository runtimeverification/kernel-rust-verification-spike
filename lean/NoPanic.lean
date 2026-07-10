-- No-panic theorem statements for the (union-free subset of the) Binder
-- deserializer, as translated by Aeneas from
--   llbc/spike_binder_reduced-charon-909ff09a-v0.1.220.llbc
--
-- Context (see AENEAS-REPORT.md):
--   * Aeneas models every Rust function in the `Result` monad
--       inductive Result α | ok (v : α) | fail (e : Error) | div
--     A *panic* (arith overflow, div-by-zero, unreachable_unchecked, explicit
--     panic!, unwrap on None, ...) is exactly `fail`. `div` is nontermination;
--     none of these functions recurse, so `div` never arises.
--   * The "no-panic property the Binder maintainer asked for" is therefore:
--         ∀ inputs, ∃ v, f inputs = ok v          -- i.e. never `fail`
--     Note this is orthogonal to the Rust-level `Result<_, Error>`/EINVAL: a
--     clean EINVAL rejection is `ok (core.result.Result.Err EINVAL)` — still
--     `ok` at the panic level. That is the whole point: reject, don't crash.
--
-- The union-based deserializer core (read_from, read_from_inner, as_ref, size,
-- parse_one) is ABSENT: Aeneas rejects `union` types, so it never reached Lean.
-- Its no-panic theorem cannot even be *stated* here yet; see the note at the end.

import SpikeBinderReduced

open Aeneas Aeneas.Std Result
open spike_binder_reduced

namespace NoPanic

/-! ## 1. `size_check` — the offset/length bounds validator.

    Fully concrete: `checked_add` (→ Option, total), `wrapping_add` (total),
    then a pure if/else. No opaque dependency, no fallible op. Unconditional
    no-panic. This is the EASIEST and the strongest result: it holds for ALL
    inputs with no side conditions. -/

theorem size_check_no_panic (offset size buffer_size : Std.Usize) :
    ∃ r, size_check offset size buffer_size = ok r := by
  simp only [size_check, lift, bind_tc_ok]
  split_ifs <;> exact ⟨_, rfl⟩

/-! ## 2. `is_aligned value to1` — `value % to1 == 0`.

    `%` on machine integers is `fail divisionByZero` when the divisor is 0
    (Aeneas.Std.UScalar.rem). So no-panic holds *iff* `to1 ≠ 0`; it is FALSE
    for `to1 = 0`. Both directions below. In the kernel `is_aligned` is only ever
    called with a nonzero power-of-two constant, so the precondition is a real
    (but, at this extracted boundary, unenforced) caller obligation. -/

theorem is_aligned_no_panic (value to1 : Std.Usize) (hto : to1.val ≠ 0) :
    ∃ b, is_aligned value to1 = ok b := by
  simp only [is_aligned, HMod.hMod, UScalar.rem]
  split
  · simp only [bind_tc_ok]; exact ⟨_, rfl⟩
  · rename_i h; exact absurd (by simpa using h) hto

-- The precondition is necessary: with `to1 = 0` the function genuinely panics.
theorem is_aligned_panics_on_zero (value : Std.Usize) :
    is_aligned value 0#usize = fail .divisionByZero := by
  simp [is_aligned, HMod.hMod, UScalar.rem]

/-! ## 3. `type_to_size type_` — tag → object size, else `None`.

    Looks trivially total, but every "known tag" arm calls `core.mem.size_of`,
    which Aeneas emitted as an OPAQUE AXIOM `: Result Std.Usize` (it is not
    mapped to a concrete Std builtin in this extraction). So its result — even
    whether it is `ok` at all — is unknown. No-panic is therefore provable only
    *modulo* the assumption that `size_of` itself never panics. The invalid-tag
    arm (`ok none`) needs no assumption. -/

theorem type_to_size_no_panic
    (hsz : ∀ T, ∃ n, core.mem.size_of T = ok n)
    (type_ : Std.U32) :
    ∃ r, type_to_size type_ = ok r := by
  unfold type_to_size
  split
  all_goals
    first
    | exact ⟨none, rfl⟩
    | (obtain ⟨n, hn⟩ := hsz _
       rw [hn]
       simp only [bind_tc_ok]
       exact ⟨some n, rfl⟩)

/-! ## 4. `ptr_align value` — round `value` up to a `usize` boundary.

    The HARDEST of the tractable four. It depends on THREE opaque axioms plus a
    fallible subtraction:
      * `core.mem.size_of Std.Usize`                     (opaque `Result`)
      * `i - 1#usize`                                    (underflows/`fail` if i = 0)
      * `core.option...Try.branch` / `...from_residual`  (the `?` on `Option`
                                                          was left as opaque
                                                          Try-trait axioms)
    Proving no-panic needs a model of the Try trait AND `size_of Usize = ok n`
    with `n ≥ 1` AND that `branch` returns `Continue`. Left as `sorry`: this maps
    the difficulty, it is not meant to be discharged in this spike. -/

theorem ptr_align_no_panic
    (hsz : ∃ n, core.mem.size_of Std.Usize = ok n ∧ 1 ≤ n.val)
    -- (plus, in reality, totality + `Continue`-ness of the opaque Try axioms)
    (value : Std.Usize) :
    ∃ r, ptr_align value = ok r := by
  sorry

/-! ## 5. `parse_one` / `read_from` / `read_from_inner` / `as_ref` / `size`.

    NOT TRANSLATED. These are the union type-punning core (`BinderObject` is a
    `union`; `read_from_inner` casts `MaybeUninit<BinderObject>` to
    `&mut [u8; 40]`). Aeneas aborts on `union` types
    (`TypesAnalysis.ml:514`, "unions are not supported") before emitting any
    Lean, so there is no Lean definition of `parse_one` to state a theorem
    against. The maintainer's real target — "for all byte inputs, `parse_one`
    never panics" — is currently *unreachable* through the Aeneas→Lean path.
    See AENEAS-REPORT.md §"distance to no-panic on parse_one". -/

-- theorem parse_one_no_panic (bytes : Std.Slice Std.U8) :
--     ∃ r, parse_one bytes = ok r := ...   -- `parse_one` does not exist in Lean

end NoPanic
