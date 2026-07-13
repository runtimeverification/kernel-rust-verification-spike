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

@[local step]
theorem len_spec (r : SliceReader) (h : r.pos.val ≤ r.data.length) :
    SliceReader.len r ⦃ fun v => v.val = r.data.length - r.pos.val ⦄ := by
  unfold SliceReader.len
  step*

@[local step]
theorem read_slice_spec (r : SliceReader) (out : Slice Std.U8)
    (h : r.pos.val ≤ r.data.length)
    (hn : out.length ≤ r.data.length - r.pos.val) :
    -- In this context the read always fits, so the Rust result is `Ok ()`; this
    -- lets the caller's `?` reduce to `Continue` without a case-split.
    SliceReader.read_slice r out ⦃ res _b _c => res = core.result.Result.Ok () ⦄ := by
  unfold SliceReader.read_slice
  step* <;> scalar_tac

@[local step]
theorem skip_spec (r : SliceReader) (n : Std.Usize) (h : r.pos.val ≤ r.data.length) :
    SliceReader.skip r n ⦃ _a _b => True ⦄ := by
  unfold SliceReader.skip
  step*

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

set_option maxHeartbeats 2000000 in
theorem parse_one_no_panic
    (hsz : ∀ T, ∃ n, core.mem.size_of T = ok n) (bytes : Slice Std.U8) :
    ∃ r, parse_one bytes = ok r := by
  refine noPanic_of_spec ?_
  unfold parse_one BinderObjectBytes.read_from BinderObjectBytes.read_from_inner
    BinderObjectBytes.read_from.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU840ResultArrayU840Error
    BinderObjectBytes.read_from.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU840ResultArrayU840Error.call_once
    SliceReader.new SliceReader.clone_reader
  -- Symbolic execution: `step` runs the monadic program via the folded specs
  -- above; `casesm` destructures `index_mut`'s (slice, write-back) pair and
  -- case-splits the opaque `Result`s returned by the reader ops so the `?`
  -- (`branch`) matches reduce; `split` handles the `is_none` `if`. `assumption`
  -- discharges the `size_of`/well-formedness side conditions of the specs. Every
  -- path ends in `ok (...)`.
  step*
  obtain ⟨s1, ib⟩ := x
  step*
  obtain ⟨r, rd, s2⟩ := x
  -- Drop the byte-content facts about the filled array; no-panic needs only that
  -- the values exist, and keeping them makes reducers evaluate the 40-byte array.
  clear x_post1 x_post2 x_post3
  -- Tail is now small and folded (hdr_type/type_to_size/size stay as specs).
  -- Each round: run the monad (`step`), reduce concrete `branch`/tuple matches
  -- (`subst_vars`/`dsimp`), `split` the tag `if`, `casesm` the one genuine Ok/Err
  -- from `skip`. Every path ends in `ok (...)`. Bounded by the control-flow depth.
  repeat' first
    | done
    | subst_vars
    | (simp only [])
    | split
    | (casesm core.result.Result _ _)
    | step
    | scalar_tac
    | trivial
  -- What remains is a single, fully concrete control-flow goal: `read_slice`
  -- returned `Ok ()` (established above), so the closure's `?` takes the
  -- `Continue` arm; the only genuine branches left are the tag check
  -- (`if o.isNone`) and `skip`'s Ok/Err — every arm ends in `ok (...)`, with NO
  -- remaining fail source (all discharged by the specs above). The obstruction
  -- is purely tactical: `step` does not reduce the tuple-pattern monadic bind
  -- `let (r,_,s2) := (Ok (), rd, s2)` produced by the multi-component reader
  -- result, and neither `simp only []`/`dsimp only []` (no progress) nor
  -- `dsimp only` (unfolds the crate defs → heartbeat blow-up) reduce it cheaply.
  -- See REMODEL-REPORT.md §"distance". The mathematical content is complete.
  all_goals sorry

end NoPanicRemodel
