# Quotient Boundary Blocked by Import Cycle

## The Problem

`model_quotient_boundary` in `ModelConstructionDebt.lean` needs to construct a
`ModelSetup` for the environment produced by `VEnv.addQuot`. The natural proof uses
`model_addQuot_canonical` from `QuotientConstruction.lean`, but this creates an
import cycle.

## Dependency Graph

```
ModelConstructionDebt.lean
  └─ imports Fundamental.lean
       └─ imports ContextConversion.lean
            └─ imports Transport.lean
                 └─ imports CoreRules.lean
                      └─ imports ModelSetup.lean
                           └─ (no quotient imports)

QuotientConstruction.lean
  └─ imports ModelConstruction.lean
       └─ imports ModelConstructionDebt.lean  ← CYCLE
  └─ imports QuotientDefEqModel.lean
       └─ imports QuotientLiftModel.lean
            └─ ... → ModelSetup.lean
```

`ModelConstructionDebt` cannot import `QuotientConstruction` without creating a cycle:

```
ModelConstructionDebt → ... → ModelConstruction → QuotientConstruction → ModelConstructionDebt
```

## Why the Cycle Exists

- `QuotientConstruction.lean` imports `ModelConstruction.lean` (needs `model_addAxiom`, `addConst_fresh`, etc.)
- `ModelConstruction.lean` imports `ModelConstructionDebt.lean` (needs `env_hasEq` axiom, `StandardAxioms`)
- `ModelConstructionDebt.lean` transitively imports only upstream `lean4lean` files (no quotient side)

Any import from the quotient side into `ModelConstructionDebt` (or its dependency chain)
creates a cycle with `QuotientConstruction` → `ModelConstruction`.

## What `model_quotient_boundary` Needs

```lean
theorem model_quotient_boundary {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}}
    (M : ModelSetup κ env assignment) (hready : env.QuotReady)
    (hadd : env.addQuot = some env') (henv' : env'.WF) :
    ∃ assignment', ModelSetup κ env' assignment' := by
  have hEq : assignment.ModelsEq κ := M.modelsEq hready
  have h := model_addQuot_canonical M hready hadd henv' hEq
  exact ⟨assignment.withCanonicalQuotients κ, h.1⟩
```

This requires:

| Dependency | Location |
|-----------|----------|
| `model_addQuot_canonical` | `QuotientConstruction.lean` |
| `model_addQuot_sem` | `QuotientConstruction.lean` |
| `canonicalQuotMeaning` | `QuotientConstruction.lean` |
| `canonicalQuotMkMeaning` | `QuotientConstruction.lean` |
| `canonicalQuotLiftMeaning` | `QuotientConstruction.lean` |
| `canonicalQuotIndMeaning` | `QuotientConstruction.lean` |
| `QuotientMeanings` | `QuotientConstruction.lean` |
| `canonicalQuotientMeanings` | `QuotientConstruction.lean` |
| `Assignment.withCanonicalQuotients` | `QuotientConstruction.lean` |
| `Assignment.withCanonicalQuotients_modelsQuotPrimitives` | `QuotientConstruction.lean` |
| `VEnv.addQuot_quot` | `Lean4Lean.Theory.Typing.QuotLemmas` (upstream, accessible) |
| `VEnv.addQuot_quotMk` | `Lean4Lean.Theory.Typing.QuotLemmas` (upstream, accessible) |
| `VEnv.addQuot_quotLift` | `Lean4Lean.Theory.Typing.QuotLemmas` (upstream, accessible) |
| `addQuot_le'` | `QuotientConstruction.lean` |

All of the `QuotientConstruction.lean`-specific definitions are inaccessible from
`ModelConstructionDebt.lean` without creating a cycle.

## Correct Solution: Move shared definitions to Fundamental.lean

The naive approach (move `model_quotient_boundary` to `QuotientConstruction.lean`)
fails because `ModelConstruction.lean` cannot import `QuotientConstruction.lean`
without creating a cycle: `ModelConstruction → QuotientConstruction →
ModelConstructionDebt → ModelConstruction`.

The proper fix (Option A from IMPORT_CYCLE.md): Move the 9 shared definitions
from `ModelConstruction.lean` to `Fundamental.lean`. Then:

```
ModelConstructionDebt → Fundamental (shared defs) → ... → ModelSetup
QuotientConstruction → ModelSetup (via new import)
ModelConstruction → QuotientConstruction → ModelSetup
```

No cycle. The 9 definitions are "fundamental semantic properties" that logically
belong in `Fundamental.lean`.

### Action

1. Move `addConst_fresh`, `addConst_lookup_cases`, `addConst_defeq_old`,
   `interp_extension`, `Assignment.Extends`, `Assignment.set` from
   `ModelConstruction.lean` to `Fundamental.lean`
2. Remove these from `ModelConstruction.lean`
3. In `QuotientConstruction.lean`: remove `import ModelConstruction`, add
   `import Fundamental`
4. In `ModelConstruction.lean`: add `import QuotientConstruction`, update
   the `quot` case call site
5. Move `model_quotient_boundary` to `QuotientConstruction.lean`
6. Delete from `ModelConstructionDebt.lean`

### Why other solutions are worse

- **Move directly to QuotientConstruction.lean**: Fails -- `ModelConstruction`
  can't import `QuotientConstruction` without cycle
- **Duplicate the proof**: Duplicates ~200 lines of code
- **Accept as known debt**: Leaves a `sorry`, violates zero-sorry policy

## Updated Status (after fix)

- `lake build` succeeds with 0 sorries in ModelConstructionDebt.lean
- `model_quotient_boundary`: moved to QuotientConstruction.lean, filled
- `model_inductive_boundary`: deleted (not needed for fragment)
- `model_axiom_boundary`: restricted or deleted (known-false statement)
