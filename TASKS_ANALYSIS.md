# Task Analysis: Eq-Shadowing Sorries

## The Claim in TASKS.md

The new `TASKS.md` (written 2026-08-22) claims that Eq-shadowing cases are impossible
because:

> "Eq is the base primitive definition (verified by lean4lean's `checkPrimitiveDef.WF`).
>  User-defined constants **cannot** shadow `Eq` -- the kernel rejects it at `addConst`
>  time. Therefore `addConst_fresh hadd` gives a contradiction when
>  `ci.name = ``Eq`: `addConst_fresh hadd` says `env.constants ``Eq = none`, but
>  `Eq` is already in the environment (from kernel bootstrapping), so
>  `env.constants ``Eq = some eqConst`."

The suggested proof:
```lean
intro heq; have := addConst_fresh hadd; simp [heq] at this
```

## Why This Is Wrong

### 1. No lemma that `Eq` is always present

Searching the entire upstream `lean4lean` package for any lemma, definition, or
theorem about `Eq` being a bootstrapped primitive yields **zero results**:

- No `checkPrimitiveDef` definition exists in the codebase
- No theorem states `env.constants ``Eq = some eqConst` for well-formed environments
- The empty `VEnv` has `constants _ := none`
- `VEnv.addConst` can legally add `Eq` when it is not yet present

The TASKS.md invokes a meta-level claim about Lean's kernel (`checkPrimitiveDef.WF`)
that has no formal representation in the model.

### 2. `addConst_fresh` does not produce a contradiction

`addConst_fresh hadd` proves `env.constants ci.name = none`. With
`heq : ci.name = ``Eq`, this gives `env.constants ``Eq = none`.

This is **not contradictory**. In the model's induction, the base environment is
the empty environment (`VEnv.empty`), which has `constants _ := none`. The
`model_of_wfHistory_withAxioms` induction builds environments incrementally:

```
empty → axioms → definitions → opaques → quot
```

`Eq` is added by the `quot` step (via `addQuot`). Before `quot`, `Eq` is NOT
in the environment. So `addConst` CAN succeed for a name `Eq` before `quot`.

### 3. The environments in the model are abstract

The model's `VEnv` is an abstract record with `constants : Name → Option VConstant`.
There is no requirement that `Eq` be present in every environment. The `QuotReady`
predicate explicitly checks for `Eq`'s presence, and is false for the empty
environment and for environments before `addQuot`.

## What Would Be Needed to Make the TASKS.md Approach Work

### Option A: Add a kernel-level axiom

Add a theorem (upstream, in `VEnv.lean` or similar):
```lean
theorem env_hasEq (env : VEnv) (h : env.WF) : env.constants ``Eq = some eqConst := ...
```
This would need to be justified by reference to Lean's kernel bootstrapping,
which is outside the model's formal system.

### Option B: Strengthen `AxiomMeaning` (previous TASKS.md approach)

Add an `eq_valid` field to `AxiomMeaning` requiring the semantic value to
satisfy the `truthValue (a = b)` property. This is the only approach that
doesn't require kernel-level assumptions.

## Current State of the Codebase

| File | Sorries | Filler Status |
|------|---------|---------------|
| `ModelConstruction.lean:235` | `model_addAxiom` Eq-shadowing | Unprovable (no Eq-always-present lemma) |
| `ModelConstruction.lean:471` | Defn Eq-shadowing | Unprovable (same) |
| `ModelConstruction.lean:517` | Opaque Eq-shadowing | Unprovable (same) |
| `ModelConstructionDebt.lean:30` | `model_axiom_boundary` | Intentionally false (needs `IsStandardAxiom` restriction) |
| `ModelConstructionDebt.lean:39` | `model_inductive_boundary` | Blocked by upstream `sorry` (can be deleted for fragment) |
| `ModelConstructionDebt.lean:56` | `model_quotient_boundary` | Blocked by missing invariant (needs `modelsEq` in induction) |

## Recommendation

The TASKS.md approach of deriving a contradiction is not viable without upstream
changes. The options are:

1. **Delete the Eq-shadowing cases** from `ModelConstruction.lean` (they represent
   a theoretical concern that doesn't apply to the fragment). This would leave 0
   sorries in `ModelConstruction.lean`.

2. **Add a lemma** `env_hasEq` to the upstream lean4lean package, then use the
   TASKS.md's contradiction proof.

3. **Strengthen `AxiomMeaning`** with an `eq_valid` field, which fills all 3
   Eq-shadowing cases without kernel assumptions.

Option 1 is the simplest and matches the fragment approach (TASKS.md says
"the model does NOT need to handle general inductive types" and Eq is handled
as a primitive).
