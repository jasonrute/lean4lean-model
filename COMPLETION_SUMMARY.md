# Completion Summary

## Task
Eliminate `model_axiom_boundary` sorry by tightening the model to standard axioms only.

## Result: DONE. Build passes. Zero sorries in fragment code.

## What was done

### 1. Deleted `model_axiom_boundary` from `ModelConstructionDebt.lean`

The theorem was a "known-false placeholder" -- the statement is false for arbitrary axioms
(e.g. `VExpr.false`). Deleted entirely along with its doc comment.

### 2. Tightened `model_of_wfHistory` to standard axioms

`model_of_wfHistory` now delegates to `model_of_wfHistory_standard`, requiring:
- `handler : StandardAxiom.Handler κ` (for constructing semantic meanings)
- `haxioms : AxiomsSatisfy IsStandardAxiom ds` (only standard axioms allowed)

### 3. Updated `model_of_wf` in `ModelConstruction.lean`

`model_of_wf` now takes `handler` and `haxioms` arguments. Uses `Classical.choose` to
extract `ds` from `H : env.WF` for the `haxioms` type, since `Exists` elimination can't
be used in binder types.

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

### 4. Updated `Consistency.lean`

`consistency` now takes `handler` and `haxioms` as explicit arguments. The soundness
theorem is now honest: it only claims consistency for environments with standard axioms.

```lean
theorem consistency {κ : ℕ → Cardinal.{u}} (hlarge : OmegaInaccessibles.{u}) {env : VEnv}
    (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible)
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
```

## Build result

```
Build completed successfully (1011 jobs).
```

Zero sorries in modified files. Only upstream `sorry` warnings remain (Inductive.lean,
InductiveLemmas.lean, Injectivity.lean, UniqueTyping.lean) -- none were modified.

## Files modified

| File | Changes |
|------|---------|
| `Lean4LeanModel/ModelConstructionDebt.lean` | Deleted `model_axiom_boundary`; updated module doc |
| `Lean4LeanModel/ModelConstruction.lean` | Updated `model_of_wfHistory` and `model_of_wf` signatures; filled modelsEq blocks |
| `Lean4LeanModel/Consistency.lean` | Added `handler` and `haxioms` arguments; updated doc comment |
| `TASKS.md` | Updated to reflect completed work |

## Remaining concerns

| Issue | Description | Action needed |
|---|---|---|
| `Classical.choose` in signatures | Used to extract `ds` from `env.WF` since `Exists` can't be projected in binder types | Standard Lean axiom; acceptable for now |
| `induct` case `sorry` | `VInductDecl.WF` still sorry upstream | Separate task: revert T-Ind |
