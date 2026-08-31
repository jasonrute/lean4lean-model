/-
# Soundness: Kernel → Model

The final theorem: an export file that passes structural validation and
lean4lean verification cannot prove `False` in the model.

This file stubs out the end-to-end soundness theorem. Each `sorry` represents
a concrete piece of work.

The proof composes:
1. `Lean4Lean.Soundness.whole_system_soundness` (structural validation → model never proves False)
2. `Lean4LeanModel.Consistency.consistency` (model never proves False, given ω inaccessible cardinals)

Both are sorried. The gap between them is the verification layer:
connecting the lean4lean verification VEnv to the model's semantic VEnv.
-/

import Lean4LeanModel.Consistency
import Lean4LeanModel.ModelConstruction
import Lean4LeanModel.StandardAxioms
import Lean4Lean.Soundness

open Lean4Lean
open Lean4LeanModel

/-! ## Soundness theorem stubs

These are the big theorems. Each is sorried.
-/

/--
**Final theorem: End-to-end soundness.**

If an export file passes structural validation (`ExportCheck`) and
lean4lean verification, then the model never proves `False`.

The proof:
1. `whole_system_soundness` (from `Lean4Lean.Soundness`) proves:
   structural validation → kernel verification → model never proves False
2. `consistency` (from `Lean4LeanModel.Consistency`) proves:
   model never proves False (given ω inaccessible cardinals)

Together, these establish that the entire pipeline is sound:
no export file that passes the checks can lead to a proof of False
in either the kernel or the model.

**Both component theorems are sorried.** This theorem cannot be proven
until `whole_system_soundness` and `consistency` are filled in.
-/
theorem end_to_end_soundness (p : Soundness.ParsedExport)
    (hreplay : ∃ env, Soundness.replay p = some env) :
    Soundness.exportCheckPasses p →
    (∃ env, Soundness.replay p = some env ∧
      ((∀ (ci : ConstantInfo), Soundness.kernel_check env ci →
        ∃ (ves' : VEnvs), ves'.WF env ∧
          ∃ (p' T' : VExpr), Soundness.TrExprS (buildVEnv env) [] [] (.const ci.name []) p' ∧
            Soundness.TrExprS (buildVEnv env) [] [] ci.type T'))) ∧
      ¬ ∃ (e : VExpr), ((buildVEnv env).venv .safe).HasType 0 [] e Soundness.falseConst)) :=
by
  intro _h
  rcases hreplay with ⟨env, hreplay_eq⟩
  have hws := whole_system_soundness p ⟨env, hreplay_eq⟩
  rcases hws with ⟨hforall, hcons⟩
  exact ⟨env, hreplay_eq, hforall, hcons⟩
