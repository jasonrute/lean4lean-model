import Lean4LeanModel.ModelConstruction
import Lean4Lean.Theory.Typing.Lemmas

/-!
# The target theorem

Consistency of Lean's type theory, relative to the existence of `ω` inaccessible cardinals --
the soundness theorem of *The Type Theory of Lean*.

The type theory itself is the one formalized in `Lean4Lean.Theory`: `VExpr` is the term syntax,
`VEnv` the declaration environment, `VEnv.WF` says the environment was built by well-founded
declarations (`VDecl.WF`), and `VEnv.HasType` is the typing judgment.

The final contradiction is proved from semantic soundness. Local declaration-model placeholders are
isolated in `ModelConstructionDebt`; the semantic stack also depends on the explicitly audited
upstream `sorry` theorems described in `Upstream`.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

/--
**Consistency statement.** Given `ω` inaccessible cardinals and that the declaration history
contains only standard axioms, no well-formed environment proves `False` -- in any number `U`
of universe parameters, in the empty local context.
-/
theorem consistency {κ : ℕ → Cardinal.{u}} {env : VEnv} (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible)
    (handler : StandardAxiom.Handler κ) (henv : env.WF)
    (haxioms : AxiomsSatisfy IsStandardAxiom (Classical.choose henv))
    (U : Nat) : ¬ ∃ e, env.HasType U [] e VExpr.false := by
  obtain ⟨assignment, M⟩ := model_of_wf hκ hi handler henv haxioms
  rintro ⟨e, he⟩
  let L := List.replicate U 0
  have heL : env.HasType L.length [] e VExpr.false := by
    simpa [L] using he
  have hmem := fundamental_hasType M heL trivial (ModelsCtx.nil (L := L))
  rw [interp_false_eq_empty κ env assignment L] at hmem
  simp at hmem

end Lean4LeanModel
