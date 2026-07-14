import Lake
open Lake DSL

-- Depends on the Aeneas Lean standard library, taken from the local Aeneas
-- checkout used for this spike:
--   ~/aeneas-project/aeneas  @ c2015b86 (2026-07-09), charon-pin 909ff09a (v0.1.220)
-- The Aeneas lib itself pulls in mathlib v4.31.0 (see its lakefile). Build it
-- once (cd there; `lake exe cache get && lake build Aeneas`) before building here.
require aeneas from
  "../../aeneas-project/aeneas/backends/lean"

package «spike_binder_verif» where

@[default_target] lean_lib «SpikeBinderReduced» where

@[default_target] lean_lib «NoPanic» where

@[default_target] lean_lib «SpikeBinderRemodel» where

@[default_target] lean_lib «NoPanicRemodel» where
