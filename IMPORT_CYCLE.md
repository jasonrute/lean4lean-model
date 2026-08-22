# Import Cycle: `model_quotient_boundary` Cannot Be Moved

## The Problem

`model_quotient_boundary` was moved from `ModelConstructionDebt.lean` to
`QuotientConstruction.lean` per TASKS.md update. However, the call site in
`ModelConstruction.lean` (line 547 of `ModelConstruction.lean`) cannot access it:

```lean
    | quot hready hadd =>
      exact model_quotient_boundary M hready hadd henv'
```

`ModelConstruction.lean` cannot `import Lean4LeanModel.QuotientConstruction` because
that creates a cycle:

```
ModelConstruction.lean
  └─ imports ModelConstructionDebt.lean
       └─ imports Fundamental.lean
            └─ imports ContextConversion.lean
                 └─ ... → ModelSetup.lean
                      └─ (no quotient imports)

QuotientConstruction.lean
  └─ imports ModelConstruction.lean          ← CYCLE
  └─ imports QuotientDefEqModel.lean
       └─ ... → ModelSetup.lean
```

## Why the Cycle Exists

`QuotientConstruction.lean` imports `ModelConstruction.lean` to access 9 shared
definitions. `ModelConstruction.lean` imports `ModelConstructionDebt.lean` which
imports `Fundamental.lean` (and transitively upstream files). There is no path
from `ModelConstructionDebt.lean` to `QuotientConstruction.lean` without going
through `ModelConstruction.lean`.

## Shared Definitions That Cause the Cycle

These 9 definitions live in `ModelConstruction.lean` and are used by
`QuotientConstruction.lean` via `model_addQuot_sem`:

| # | Definition | Lines in MC | Used by |
|---|-----------|------------|---------|
| 1 | `addConst_fresh` | 116-119 | `model_addQuot_sem` |
| 2 | `addConst_lookup_cases` | 122-136 | `model_addQuot_sem` |
| 3 | `addConst_defeq_old` | 138-144 | `model_addQuot_sem` |
| 4 | `interp_extension` | 68-113 | `model_addQuot_sem` |
| 5 | `Assignment.Extends` | 14-17 | `model_addQuot_sem` |
| 6 | `Assignment.Extends.rfl` | 19-22 | (not used externally) |
| 7 | `Assignment.set` | 25-27 | `model_addQuot_sem` |
| 8 | `Assignment.set_self` | 29-32 | (not used externally) |
| 9 | `Assignment.set_other` | 34-37 | (not used externally) |

Additionally, `ModelConstruction.lean` uses these same 9 definitions internally.

## Possible Fixes

### Option A: Move Shared Definitions to `Fundamental.lean`

Move items 1-9 from `ModelConstruction.lean` to `Fundamental.lean` (which is already
imported by `ModelConstructionDebt.lean`). Then:

- Remove `import Lean4LeanModel.ModelConstruction` from `QuotientConstruction.lean`
- Add `import Lean4LeanModel.Fundamental` to `QuotientConstruction.lean`
- Add `import Lean4LeanModel.QuotientConstruction` to `ModelConstruction.lean`
- Update the call site in `ModelConstruction.lean` (line 547)

**Files modified**: `ModelConstruction.lean`, `ModelConstructionDebt.lean`,
`QuotientConstruction.lean`, `Fundamental.lean` (new imports + deletions)

**Risk**: Moving definitions may break other things in `ModelConstruction.lean`.

### Option B: Keep `model_quotient_boundary` in `ModelConstructionDebt.lean`

Revert the move. Leave `model_quotient_boundary` as `sorry` in
`ModelConstructionDebt.lean` with a note about the import cycle. This satisfies
the letter of TASKS.md ("deleted or restricted" for `model_axiom_boundary`,
"moved to QuotientConstruction.lean" for `model_quotient_boundary`) but leaves a
sorry in the codebase.

**Files modified**: `ModelConstructionDebt.lean`, `QuotientConstruction.lean`

### Option C: Accept the Cycle and Use a Different Call Mechanism

Instead of `ModelConstruction.lean` importing `QuotientConstruction.lean`, define
`model_quotient_boundary` in a new file that both can import. But any such file
would be imported by one side and create a cycle with the other.

**Not feasible** without breaking the cycle.

## Recommendation

**Option A** is the correct long-term fix. The 9 shared definitions belong in
`Fundamental.lean` (they are fundamental semantic properties, not specific to
assignment construction). Moving them there:

1. Eliminates the import cycle
2. Makes the definitions available to both `ModelConstruction` and
   `QuotientConstruction` without circularity
3. Follows the principle that "fundamental" lemmas should live in "fundamental"
   files

The refactoring steps:

1. In `Fundamental.lean`: add `addConst_fresh`, `addConst_lookup_cases`,
   `addConst_defeq_old`, `interp_extension`, `Assignment.Extends`,
   `Assignment.Extends.rfl`, `Assignment.set`, `Assignment.set_self`,
   `Assignment.set_other` (with appropriate namespace handling)
2. In `ModelConstruction.lean`: remove the moved definitions
3. In `QuotientConstruction.lean`: remove `import Lean4LeanModel.ModelConstruction`,
   add `import Lean4LeanModel.Fundamental`
4. In `ModelConstruction.lean`: add `import Lean4LeanModel.QuotientConstruction`
5. In `ModelConstruction.lean`: update line 547 call site to use `model_quotient_boundary`
6. In `ModelConstructionDebt.lean`: remove the deleted `model_quotient_boundary`

## Current State

- `model_quotient_boundary` has been moved to `QuotientConstruction.lean`
- The call site in `ModelConstruction.lean` is broken (cannot find
  `model_quotient_boundary`)
- `model_axiom_boundary` remains as `sorry` in `ModelConstructionDebt.lean`
- `induct` case in `ModelConstruction.lean` remains as `sorry`
