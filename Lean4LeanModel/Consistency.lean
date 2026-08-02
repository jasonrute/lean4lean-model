import Lean4LeanModel.CoreRules
import Lean4Lean.Theory.Typing.Lemmas

/-!
# The target theorem

Consistency of Lean's type theory, relative to the existence of `ω` inaccessible cardinals --
the soundness theorem of *The Type Theory of Lean*.

The type theory itself is the one formalized in `Lean4Lean.Theory`: `VExpr` is the term syntax,
`VEnv` the declaration environment, `VEnv.WF` says the environment was built by well-founded
declarations (`VDecl.WF`), and `VEnv.HasType` is the typing judgment.

Nothing here is proved yet; the model construction is what fills `sorry` in.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

/--
**Consistency of Lean.** Assuming `ω` inaccessible cardinals, no well-formed environment proves
`∀ (p : Prop), p` -- in any number `U` of universe parameters, in the empty local context.

The declaration-model construction intentionally retains an explicit proof hole for arbitrary
axioms while the final true statement admitting Lean's standard axioms is being specified.
-/
theorem consistency (_ : OmegaInaccessibles.{u}) {env : VEnv} (_ : env.WF) (U : Nat) :
    ¬ ∃ e, env.HasType U [] e VExpr.false := by
  sorry

end Lean4LeanModel
