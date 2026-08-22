import Lean4LeanModel.Fundamental
import Lean4LeanModel.StandardAxioms
import Lean4Lean.Theory.Typing.Env

/-!
# Explicit declaration-model boundaries

- `model_inductive_boundary`: Deleted (not needed for the lean-inductive-models fragment).
- `model_quotient_boundary`: Moved to `QuotientConstruction.lean`.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

/-! ## Temporary axiom: Eq is always present

In Lean's kernel, `Eq` is a bootstrapped primitive definition verified by
`checkPrimitiveDef.WF`. The model's `VEnv` is an abstract record without this
property yet. This temporary axiom makes it explicit and unblocks the
Eq-shadowing cases. It will be replaced when kernel bootstrapping is formally modeled.
-/

/-- TEMPORARY: Eq is always present in well-formed environments.
True for the kernel's bootstrapped environment but not yet proven in the model.
Will be replaced when kernel bootstrapping is formally modeled. -/
axiom env_hasEq (env : VEnv) (h : env.WF) : env.constants ``Eq = some eqConst

end Lean4LeanModel
