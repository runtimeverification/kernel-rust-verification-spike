-- No-panic theorems for the UNION-FREE REMODEL of the Binder deserializer,
-- translated by Aeneas from
--   llbc/spike_binder_remodel-charon-909ff09a-v0.1.220.llbc
--
-- Panic model (as in NoPanic.lean): Aeneas puts every function in the `Result`
-- monad `ok v | fail e | div`. A panic (overflow, div-by-zero, out-of-bounds
-- index, unwrap on None, ...) is exactly `fail`; `div` never arises (nothing
-- recurses). No-panic is `∀ inputs, ∃ v, f inputs = ok v`. A clean EINVAL
-- rejection is `ok (Result.Err EINVAL)` — still `ok`, i.e. "reject, don't crash".
--
-- Unlike NoPanic.lean (the union-free VALIDATORS only), here the whole parse
-- path is present, so parse_one's no-panic theorem can finally be stated.

import SpikeBinderRemodel

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open spike_binder_remodel

namespace NoPanicRemodel

/- =====================================================================
   Ported validator theorems (identical to NoPanic.lean, against the
   remodel's copies) so everything lives against one codebase.
   ===================================================================== -/

theorem size_check_no_panic (offset size buffer_size : Std.Usize) :
    ∃ r, size_check offset size buffer_size = ok r := by
  simp only [size_check, lift, bind_tc_ok]
  split_ifs <;> exact ⟨_, rfl⟩

theorem is_aligned_no_panic (value to1 : Std.Usize) (hto : to1.val ≠ 0) :
    ∃ b, is_aligned value to1 = ok b := by
  simp only [is_aligned, HMod.hMod, UScalar.rem]
  split
  · simp only [bind_tc_ok]; exact ⟨_, rfl⟩
  · rename_i h; exact absurd (by simpa using h) hto

theorem is_aligned_panics_on_zero (value : Std.Usize) :
    is_aligned value 0#usize = fail .divisionByZero := by
  simp [is_aligned, HMod.hMod, UScalar.rem]

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

/- =====================================================================
   Accessors (the REMODEL of `as_ref`): each reads fixed literal offsets
   (< 40) from a fixed-size `Array U8 40` and decodes with the total
   `from_le_bytes`. No-panic is mechanical: the only fail source is an
   out-of-bounds array index, impossible for literal indices < 40.
   ===================================================================== -/

-- No-panic (`∃ v, m = ok v`) is exactly the `spec _ (fun _ => True)` postcondition.
theorem noPanic_of_spec {α} {m : Result α} (h : m ⦃ fun _ => True ⦄) :
    ∃ v, m = ok v := by
  obtain ⟨v, hv, _⟩ := spec_imp_exists h; exact ⟨v, hv⟩

/- =====================================================================
   `SliceReader` no-fail specs, used as `step` lemmas below.
   A reader is well-formed when `pos ≤ data.len`; then `len` (a subtraction)
   cannot underflow and `read_slice`/`skip` cannot fail. `parse_one` only ever
   uses readers with `pos = 0`, which trivially satisfy this.
   ===================================================================== -/

-- `parse_one` only ever uses readers with `pos = 0`. On such a reader every op
-- is UNCONDITIONALLY total: `len`'s subtraction is `data.len - 0` (no underflow),
-- and `read_slice`/`skip` return a clean `Err` *value* rather than failing when
-- the length is exceeded. Precondition-free specs let `step*` apply them and
-- destructure their tuple results (its `introOutputs` fires for spec applications
-- with no side goal), exactly as in Aeneas's own tuple-bind tests.
@[local step]
theorem len_zero (data : Slice Std.U8) :
    SliceReader.len ⟨data, 0#usize⟩ ⦃ fun v => v.val = data.length ⦄ := by
  unfold SliceReader.len; step*

@[local step]
theorem read_slice_zero (data out : Slice Std.U8) :
    SliceReader.read_slice ⟨data, 0#usize⟩ out ⦃ _a _b _c => True ⦄ := by
  unfold SliceReader.read_slice; step*

@[local step]
theorem skip_zero (data : Slice Std.U8) (n : Std.Usize) :
    SliceReader.skip ⟨data, 0#usize⟩ n ⦃ _a _b => True ⦄ := by
  unfold SliceReader.skip; step*

theorem hdr_type_no_panic (self : BinderObjectBytes) : ∃ v, self.hdr_type = ok v :=
  noPanic_of_spec (by unfold BinderObjectBytes.hdr_type; step*)

theorem fbo_flags_no_panic (self : BinderObjectBytes) : ∃ v, self.fbo_flags = ok v :=
  noPanic_of_spec (by unfold BinderObjectBytes.fbo_flags; step*)
theorem fbo_binder_no_panic (self : BinderObjectBytes) : ∃ v, self.fbo_binder = ok v :=
  noPanic_of_spec (by unfold BinderObjectBytes.fbo_binder; step*)
theorem fbo_handle_no_panic (self : BinderObjectBytes) : ∃ v, self.fbo_handle = ok v :=
  noPanic_of_spec (by unfold BinderObjectBytes.fbo_handle; step*)
theorem fbo_cookie_no_panic (self : BinderObjectBytes) : ∃ v, self.fbo_cookie = ok v :=
  noPanic_of_spec (by unfold BinderObjectBytes.fbo_cookie; step*)

theorem fdo_fd_no_panic (self : BinderObjectBytes) : ∃ v, self.fdo_fd = ok v :=
  noPanic_of_spec (by unfold BinderObjectBytes.fdo_fd; step*)
theorem fdo_cookie_no_panic (self : BinderObjectBytes) : ∃ v, self.fdo_cookie = ok v :=
  noPanic_of_spec (by unfold BinderObjectBytes.fdo_cookie; step*)

theorem bbo_flags_no_panic (self : BinderObjectBytes) : ∃ v, self.bbo_flags = ok v :=
  noPanic_of_spec (by unfold BinderObjectBytes.bbo_flags; step*)
theorem bbo_buffer_no_panic (self : BinderObjectBytes) : ∃ v, self.bbo_buffer = ok v :=
  noPanic_of_spec (by unfold BinderObjectBytes.bbo_buffer; step*)
theorem bbo_length_no_panic (self : BinderObjectBytes) : ∃ v, self.bbo_length = ok v :=
  noPanic_of_spec (by unfold BinderObjectBytes.bbo_length; step*)
theorem bbo_parent_no_panic (self : BinderObjectBytes) : ∃ v, self.bbo_parent = ok v :=
  noPanic_of_spec (by unfold BinderObjectBytes.bbo_parent; step*)
theorem bbo_parent_offset_no_panic (self : BinderObjectBytes) : ∃ v, self.bbo_parent_offset = ok v :=
  noPanic_of_spec (by unfold BinderObjectBytes.bbo_parent_offset; step*)

theorem fdao_num_fds_no_panic (self : BinderObjectBytes) : ∃ v, self.fdao_num_fds = ok v :=
  noPanic_of_spec (by unfold BinderObjectBytes.fdao_num_fds; step*)
theorem fdao_parent_no_panic (self : BinderObjectBytes) : ∃ v, self.fdao_parent = ok v :=
  noPanic_of_spec (by unfold BinderObjectBytes.fdao_parent; step*)
theorem fdao_parent_offset_no_panic (self : BinderObjectBytes) : ∃ v, self.fdao_parent_offset = ok v :=
  noPanic_of_spec (by unfold BinderObjectBytes.fdao_parent_offset; step*)

/- =====================================================================
   `size`: reads the tag then maps it via `type_to_size`. No-panic modulo
   the same `size_of` totality assumption `type_to_size` needs.
   ===================================================================== -/

theorem size_no_panic
    (hsz : ∀ T, ∃ n, core.mem.size_of T = ok n) (self : BinderObjectBytes) :
    ∃ v, self.size = ok v := by
  obtain ⟨t, ht⟩ := hdr_type_no_panic self
  obtain ⟨o, ho⟩ := type_to_size_no_panic hsz t
  simp only [BinderObjectBytes.size, ht, bind_tc_ok, ho]
  cases o <;> exact ⟨_, rfl⟩

/- Black-box `step` specs (no-fail) for the crate functions used inside
   `read_from`/`parse_one`. Keeping them folded avoids expanding the 4 array
   reads of `hdr_type` and the 9-way tag `match` of `type_to_size` at every use
   site (which otherwise blows up symbolic execution). -/

@[local step]
theorem hdr_type_spec (self : BinderObjectBytes) : self.hdr_type ⦃ fun _ => True ⦄ :=
  exists_imp_spec (by obtain ⟨v, hv⟩ := hdr_type_no_panic self; exact ⟨v, hv, trivial⟩)

@[local step]
theorem type_to_size_spec (t : Std.U32)
    (hsz : ∀ T, ∃ n, core.mem.size_of T = ok n) : type_to_size t ⦃ fun _ => True ⦄ :=
  exists_imp_spec (by obtain ⟨v, hv⟩ := type_to_size_no_panic hsz t; exact ⟨v, hv, trivial⟩)

@[local step]
theorem size_spec (self : BinderObjectBytes)
    (hsz : ∀ T, ∃ n, core.mem.size_of T = ok n) : self.size ⦃ fun _ => True ⦄ :=
  exists_imp_spec (by obtain ⟨v, hv⟩ := size_no_panic hsz self; exact ⟨v, hv, trivial⟩)

/- =====================================================================
   The target: parse_one never panics.

   `parse_one` reads a fresh reader (pos = 0), so every `SliceReader.len`
   subtraction `data.len - pos` is `data.len - 0` (no underflow); all array/
   slice indices are bounded by `read_len = min(40, data.len)`; and the only
   opaque dependency is `size_of` (via `type_to_size`). We discharge `size_of`
   by pulling its four concrete results out of `hsz`, which makes `type_to_size`
   fully concrete; everything else is closed by symbolic execution (`step*`) with
   arithmetic side-goals dispatched by `scalar_tac`.
   ===================================================================== -/

set_option maxHeartbeats 4000000 in
theorem parse_one_no_panic
    (hsz : ∀ T, ∃ n, core.mem.size_of T = ok n) (bytes : Slice Std.U8) :
    ∃ r, parse_one bytes = ok r := by
  refine noPanic_of_spec ?_
  unfold parse_one BinderObjectBytes.read_from BinderObjectBytes.read_from_inner
    BinderObjectBytes.read_from.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU840ResultArrayU840Error
    BinderObjectBytes.read_from.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU840ResultArrayU840Error.call_once
    SliceReader.new SliceReader.clone_reader
  -- `index_mut`'s and `read_slice`'s specs return tuples, but `step`'s output-
  -- destructuring leaves the (slice, write-back) / (result, reader, slice) pair as
  -- a single hypothesis here; destructure them by hand so `step` can continue.
  step*
  obtain ⟨s1, ib⟩ := x
  -- byte-content facts about the filled array are irrelevant to no-panic, and
  -- keeping them makes the reducers evaluate the 40-byte array.
  clear x_post1 x_post2 x_post3
  step*
  obtain ⟨r, rd, s2⟩ := x
  step*
  cases r
  -- What remains is the `?`/`branch` cascade (the tag check `if o.isNone`, and
  -- `skip`'s Ok/Err). Each round: reduce the `branch`/tuple matches over
  -- constructors (`simp only [] at *`), run the monad (`step*`), destructure
  -- `skip`'s result pair / case its `Result` (`casesm`), split the `if` (`split`).
  -- Every arm ends in `ok (...)`. Bounded by the control-flow depth.
  iterate 12
    (all_goals (try (simp only [] at *));
     all_goals (try step*);
     all_goals (try (casesm _ × _));
     all_goals (try (casesm core.result.Result _ _));
     all_goals (try split))

end NoPanicRemodel
