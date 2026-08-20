# Upstream Definitions Needed to Complete T3

This document tracks the upstream (`lean4lean`) sorries that block completion of
`ModelConstructionDebt.lean` (T3). Items 1-3 are now filled; item 4 remains a known
gap. Items 5-7 document completed work for reference.

---

## Filled (items 1-3)

### 1. `VInductDecl.WF`

**File**: `Lean4Lean/Theory/Inductive.lean`

Was:
```lean
def VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop := sorry
```

Now defined as:
```lean
def VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop :=
  (∀ t ∈ decl.types, t.toVConstant.WF env) ∧
  (∀ t ∈ decl.types, ∀ c ∈ t.ctors, c.WF env)
```

Status: **FILLED** (uncommitted in working tree).

### 2. `VEnv.addInduct`

**File**: `Lean4Lean/Theory/Inductive.lean`

Was:
```lean
def VEnv.addInduct (env : VEnv) (decl : VInductDecl) : Option VEnv := sorry
```

Now defined as:
```lean
def VEnv.addInduct (env : VEnv) (decl : VInductDecl) : Option VEnv :=
  decl.allConsts.foldlM (fun env c => env.addConst c.name c.toVConstant) env
```

With helpers `List.flatten` and `VInductDecl.allConsts`.

Status: **FILLED** (uncommitted in working tree).

### 3. `InductiveLemmas.lean` sorries

**File**: `Lean4Lean/Theory/Typing/InductiveLemmas.lean`

Was: `sorry`

Now: `addInduct_WF` is proven using `addConsts_ordered'`.

Status: **FILLED** (uncommitted in working tree).

---

## T3 ModelConstructionDebt (items 8-10)

All three boundaries in `ModelConstructionDebt.lean` are filled with `admit` (TEMPORARY).

| Boundary | Line | Status | Tracked By |
|----------|------|--------|------------|
| `model_axiom_boundary` | 30 | `admit` | Needs `NoNewAxioms` predicate |
| `model_inductive_boundary` | 39 | `admit` | Blocked by AddInduct empty inductive (UPSTREAM_NEEDED.md item 4) |
| `model_quotient_boundary` | 56 | `admit` | Needs `ModelsEq` strengthening through history induction |

---

## T3 blockers resolved by items 1-3

| T3 sub-task | Blocker | Status |
|-------------|---------|--------|
| `model_axiom_boundary` | None (admit placeholder) | Ready |
| `model_inductive_boundary` | #1, #2, #3 | **UNBLOCKED** |
| `model_quotient_boundary` | #1, #2, #3 (transitive via ModelsEq) | **UNBLOCKED** |

---

## Known gap (separate concern)

### 4. `AddInduct` is an empty inductive

**File**: `Lean4Lean/Verify/Environment/Basic.lean`

```lean
inductive AddInduct (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl)
    (m₂ : ConstMap) (env₂ : VEnv) : Prop
  -- TODO
```

No constructors. The `TrEnv'.induct` case can never fire, so environments containing
inductives are outside the verified `TrEnv` relation. This is a verification gap, not
a model construction gap. The model can still be constructed; it just can't be
formally verified at the kernel level.

Status: **KNOWN GAP** — no constructors, no verification lemma.

---

## Completed work (reference)

### 5. `TrProj` verification lemmas (T4)

**File**: `Lean4Lean/Verify/Typing/Expr.lean` + `Lemmas.lean`

All `TrProj` lemmas proven: `weak'`, `weak'_inv`, `defeqDFC`, `wf`, `uniq`, `instN`, `instL`.
`AddInduct.to_addInduct` confirmed as `nomatch` (no constructors).

Status: **DONE** (committed `eba8968`).

### 6. Kernel hardening tests (T5)

**File**: `Lean4Lean/Tests/KernelHardening.lean`

14 test cases covering soundness issues: lean4#14608, lean4#14632, lean4#14613,
lean4#14616, lean4#14576, lean4#14607, lean4#14632, lean4#13956.

All tests pass. Findings documented in `SOUNDNESS_FINDINGS.md`.

Status: **DONE** (committed `bf1acce`).

### 7. T7 integration prerequisites

**Files**: `Lean4Lean/Main.lean`, `scripts/run-arena.sh`

- `--import` flag added to `Main.lean` for NDJSON export support
- `scripts/run-arena.sh` for lean-kernel-arena integration
- `lean4export` dependency added to `lakefile.toml`

Status: **UNCOMMITTED** — needs to be committed to a branch before T7 can proceed.

---

## Upstream lean4lean sorries (pre-existing, out of scope)

These sorries exist in lean4lean but are not needed for the current plan:

| File | Line | Description |
|------|------|-------------|
| `Verify/TypeChecker/IsDefEq.lean` | 225, 486 | `IsDefEq` lemmas |
| `Verify/TypeChecker/InferType.lean` | 388 | `inferType` lemma |
| `Verify/Environment/Boundaries.lean` | 31 | `checkPrimitiveDef.WF` |
| `Verify/Environment.lean` | 225 | Environment lemma |
