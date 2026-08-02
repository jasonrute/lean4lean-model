import Lean4Lean.Theory.Typing.Env
import Mathlib.SetTheory.Cardinal.Regular

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

open Lean4Lean Cardinal

universe u

/--
`∀ (α : Sort 0), α`, i.e. `∀ (p : Prop), p`.

This is the environment-independent stand-in for `False`: a `VEnv` need not contain the `False`
inductive at all, and any proof of `False` in an environment that does yields a proof of this.
-/
def VExpr.false : VExpr := .forallE (.sort .zero) (.bvar 0)

/--
There are `ω` inaccessible cardinals: a strictly increasing `ℕ`-indexed sequence of them, one to
interpret each Lean universe `Sort 0, Sort 1, ...`.

Lean itself cannot prove this: its foundations give only `v`-many inaccessibles in universe `v`
(`Cardinal.IsInaccessible.univ`), i.e. a numeral's worth for any fixed universe, never `ω` of
them in a single `Cardinal.{u}`. That gap is exactly the consistency strength the theorem below
assumes, and is why this is a hypothesis rather than a lemma.
-/
def OmegaInaccessibles : Prop :=
  ∃ κ : ℕ → Cardinal.{u}, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible

/--
**Consistency of Lean.** Assuming `ω` inaccessible cardinals, no well-formed environment proves
`∀ (p : Prop), p` -- in any number `U` of universe parameters, in the empty local context.
-/
theorem consistency (_ : OmegaInaccessibles.{u}) {env : VEnv} (_ : env.WF) (U : Nat) :
    ¬ ∃ e, env.HasType U [] e VExpr.false := by
  sorry

end Lean4LeanModel
