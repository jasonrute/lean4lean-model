import Lean4LeanModel.Fundamental
import Lean4Lean.Theory.Typing.Env

/-!
# Explicit declaration-model boundaries

These are the only local proof holes in the construction. The axiom theorem is retained solely for
the backwards-compatible unrestricted statement; `model_of_wfHistory_standard` bypasses it via
explicit meanings for the standard three. The inductive theorem is blocked by upstream `sorry`
definitions. The quotient mathematics is complete, while its environment step still needs the
canonical equality invariant and primitive computation-rule bridge. The holes are kept in a
dedicated module so CI can reject accidental proof debt everywhere else.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

/-- **Known-false statement placeholder.** The naive theorem permits arbitrary axioms, whose
declared types need not be inhabited: adding an axiom of `VExpr.false` is a counterexample. This is
the localized axiom case requested while the true statement admitting Lean's standard axioms is
being specified. -/
theorem model_axiom_boundary {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} {ci : VConstVal}
    (M : ModelSetup κ env assignment) (hci : ci.toVConstant.WF env)
    (hadd : env.addConst ci.name ci.toVConstant = some env') (henv' : env'.WF) :
    ∃ assignment', ModelSetup κ env' assignment' := by
  sorry

/-- `VInductDecl.WF` and `VEnv.addInduct` are still defined by `sorry` upstream and expose no
constructor data from which to build the corresponding sets. -/
theorem model_inductive_boundary {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} {decl : VInductDecl}
    (M : ModelSetup κ env assignment) (hdecl : decl.WF env)
    (hadd : env.addInduct decl = some env') (henv' : env'.WF) :
    ∃ assignment', ModelSetup κ env' assignment' := by
  sorry

/-- The genuine quotient operations, their universe closure, and operation-level compatibility
with `Quot.sound` are constructed in `Quotient` and `QuotientModel`. Completing `addQuot` must wire
its four constants and the `Quot.lift` computation rule into `Assignment.WF`, while preserving the
`ModelsEq` and `ModelsQuot` invariants. The `Quot.lift` case needs canonical equality;
`VEnv.QuotReady` records only the declaration of `Eq`, not its semantic meaning. -/
theorem model_quotient_boundary {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}}
    (M : ModelSetup κ env assignment) (hready : env.QuotReady)
    (hadd : env.addQuot = some env') (henv' : env'.WF) :
    ∃ assignment', ModelSetup κ env' assignment' := by
  sorry

end Lean4LeanModel
