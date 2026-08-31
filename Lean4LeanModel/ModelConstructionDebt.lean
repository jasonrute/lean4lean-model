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

### Why this axiom cannot currently be replaced

The model's `VEnv` starts as `.empty` (`constants _ := none`). The well-foundedness
predicate `VEnv.WF` (defined in `Theory/Typing/Env.lean`) only tracks declarations
added via `VDecl.WF` constructors (`axiom`, `def`, `opaque`, `example`, `quot`).
Eq is NOT a `VDecl` -- it is a bootstrapped primitive added by the kernel *before*
any user declarations.

The base case of model construction (`ModelConstruction.lean:310-319`) confirms
this: the empty environment `⟨[], .empty⟩` satisfies `VEnv.WF` but `VEnv.empty` does
not contain `Eq`. Since `VEnv.WF` only grows from `.empty` by adding `VDecl`s, and
Eq is never added by any `VDecl.WF` constructor, no `VEnv.WF` environment can be
proven to contain Eq without modifying the Theory to add a bootstrapping phase.

### What would be needed to replace this axiom

1. **Theory change**: Add an `Eq`-bootstrapping constructor to `VEnv.WF'`
   (or a companion predicate `VEnv.Bootstrapped`), e.g.:
   ```lean
   | bootstrappedEq : VEnv.WF' ds { env with constants := fun n =>
       if n = ``Eq then some eqConst else env.constants n } env
   ```
   This constructor would represent that Eq has been added as a bootstrapped
   primitive before user code.

2. **Model change**: Update `VEnv.WF'.empty` to use `bootstrappedEq` instead
   of bare `.empty`, or add a separate bootstrapping phase that adds Eq
   before `VEnv.WF` is used.

3. **Proof**: Then `env_hasEq` follows by induction on `h : env.WF` with the
   `bootstrappedEq` case providing the Eq constant.

The upstream `checkPrimitiveDef.WF` theorem (in
`Theory/Verify/Environment/Boundaries.lean`) is also `sorry`-backed and would
need to be filled as part of this work.
-/

/-- TEMPORARY: Eq is always present in well-formed environments.
True for the kernel's bootstrapped environment but not yet proven in the model.
Will be replaced when kernel bootstrapping is formally modeled. -/
axiom env_hasEq (env : VEnv) (h : env.WF) : env.constants ``Eq = some eqConst

end Lean4LeanModel
