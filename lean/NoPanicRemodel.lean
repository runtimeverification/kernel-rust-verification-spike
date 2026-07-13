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

end NoPanicRemodel
