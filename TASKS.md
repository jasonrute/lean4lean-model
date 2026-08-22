# Task Instructions: lean4lean-model repo

## Repository state

- **Branch**: `task/fill-modelsEq` (based on `model/quotients`)
- **Upstream**: `jasonrute/lean4lean-model` (your fork, base: `digama0/lean4lean-model`)
- **Build**: `lake build` succeeds
- **Key constraint**: Do NOT modify upstream lean4lean files. Only modify files in `Lean4LeanModel/`.
- **Approach**: This model proves soundness for the "lean-inductive-models fragment" -- Lean
  without user-defined inductive types. The base `Eq` type is handled as a primitive definition
  (verified by lean4lean's `checkPrimitiveDef.WF`). The model does NOT need to handle general
  inductive types (those are eliminated externally by lean-inductive-models).

---

## Context: what the model proves

The model constructs a ZF-set semantics for Lean's type theory inside Lean itself.
`ModelSetup` (ModelSetup.lean:31) records the global invariants:

| Field | Meaning |
|-------|---------|
| `cardinals_strictMono` | Cardinal assignment is strictly monotone |
| `cardinals_inaccessible` | Each cardinal is inaccessible |
| `environmentWF` | The VEnv is well-formed |
| `assignmentWF` | The assignment validates all constants and defeqs |
| `modelsEq` | Equality in the model is classical equality (for `Eq` types) |

Every `model_add*` theorem constructs a `ModelSetup` for the extended environment.
The `modelsEq` field is the hardest -- it says that `Eq`'s interpretation in the model
reduces to truth of equality.

---

## Completed work (already done)

### Import cycle fixed

Moved 9 shared definitions from `ModelConstruction.lean` to `Fundamental.lean`:
`addConst_fresh`, `addConst_lookup_cases`, `addConst_defeq_old`, `interp_extension`,
`Assignment.Extends`, `Assignment.set`, `Assignment.set_self`, `Assignment.set_other`,
`Assignment.Extends.set_of_addConst`.

Updated imports:
- `QuotientConstruction.lean`: `import ModelConstruction` → `import Fundamental`
- `ModelConstruction.lean`: added `import QuotientConstruction`

### Task 1: `modelsEq` sorries in `ModelConstruction.lean` -- DONE

All 4 `modelsEq` sorries filled:
1. **`model_addAxiom`**: `hmodelsEq` block filled using `env_hasEq` axiom for Eq-shadowing
2. **Opaque cases** (3 places in `model_of_wfHistory_withAxioms`): `hopaque_modelsEq` filled
3. **Eq-shadowing def case**: contradiction via `env_hasEq` + `addConst_fresh`
4. **Eq-shadowing opaque case**: same contradiction pattern

Remaining `sorry` at line ~420 (`induct` case) is an upstream dependency:
`VInductDecl.WF` is still sorry upstream; the fragment doesn't need inductives.

### Task 2: `ModelConstructionDebt.lean` admits -- PARTIALLY DONE

- **`model_inductive_boundary`**: DELETED (not needed for fragment)
- **`model_quotient_boundary`**: MOVED to `QuotientConstruction.lean` and FILLED
- **`model_axiom_boundary`**: still `sorry` -- the statement is false for arbitrary axioms
  (e.g. `VExpr.false`). Needs restriction to standard axioms or deletion.

### Temporary axiom

`env_hasEq` added to `ModelConstructionDebt.lean` to unblock Eq-shadowing cases via
contradiction. Will be replaced when kernel bootstrapping is formally modeled.

---

## Completed: Eliminate `model_axiom_boundary` sorry

### Changes made

#### Step 1: Deleted `model_axiom_boundary` from `ModelConstructionDebt.lean`

Deleted the theorem and its associated doc comment. File now only contains the `env_hasEq` axiom.

#### Step 2: Tightened `model_of_wfHistory` to standard axioms

`model_of_wfHistory` now delegates to `model_of_wfHistory_standard`, requiring
`handler : StandardAxiom.Handler κ` and `haxioms : AxiomsSatisfy IsStandardAxiom ds`.

#### Step 3: Updated `model_of_wf` in `ModelConstruction.lean`

`model_of_wf` now takes `handler` and `haxioms` arguments. Uses `Classical.choose` to
extract `ds` from `H : env.WF` for the `haxioms` type.

```lean
theorem model_of_wf {κ : ℕ → Cardinal.{u}} (hκ : StrictMono κ)
    (hi : ∀ n, (κ n).IsInaccessible)
    (handler : StandardAxiom.Handler κ)
    {env : VEnv} (H : env.WF)
    (haxioms : AxiomsSatisfy IsStandardAxiom (Classical.choose H)) :
    ∃ assignment, ModelSetup κ env assignment := by
  let ds := Classical.choose H
  have hds : VEnv.WF' ds env := Classical.choose_spec H
  exact model_of_wfHistory hκ hi handler hds haxioms
```

#### Step 4: Updated `Consistency.lean`

`consistency` now takes `handler` and `haxioms` as explicit arguments. Uses
`Classical.choose henv` to match the `haxioms` type.

```lean
theorem consistency {κ : ℕ → Cardinal.{u}} (hlarge : OmegaInaccessibles.{u}) {env : VEnv}
    (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible)
    (handler : StandardAxiom.Handler κ) (henv : env.WF)
    (haxioms : AxiomsSatisfy IsStandardAxiom (Classical.choose henv))
    (U : Nat) : ¬ ∃ e, env.HasType U [] e VExpr.false := by
  obtain ⟨assignment, M⟩ := model_of_wf hκ hi handler henv haxioms
  ...
```

### Remaining issues

- `Classical.choose` is used to extract `ds` from `env.WF`. This is a standard Lean axiom.
- The `induct` case `sorry` at `ModelConstruction.lean:304` remains (upstream dependency).
