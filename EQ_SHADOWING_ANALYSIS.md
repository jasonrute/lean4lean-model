# Eq-Shadowing Analysis -- SUPERSEDED by fragment approach

**This analysis is superseded by the lean-inductive-models fragment approach.**
The conclusion that Eq-shadowing is "hard" was wrong for the fragment.

## Problem

Six sorries remain across `ModelConstruction.lean` and `ModelConstructionDebt.lean`.
Three are Eq-shadowing cases where a declaration is named `Eq`, shadowing the built-in
equality constant. The other three are boundary theorems with different blockers.

---

## Eq-Shadowing Cases (ModelConstruction.lean)

### Location

| Line | Context |
|------|---------|
| 235 | `model_addAxiom` — axiom named `Eq` |
| 471 | `model_of_wfHistory_withAxioms` defn case — def named `Eq` |
| 517 | `model_of_wfHistory_withAxioms` opaque case — opaque named `Eq` |

### What the code does

Each case follows the same pattern:

```lean
by_cases heq : ci.name = ``Eq
· -- shadowing: the declaration is named Eq
  sorry
· -- non-shadowing: ci.name ≠ Eq, Eq constant unchanged
  -- (already filled: uses M.modelsEq)
```

### Why the non-shadowing case is filled

When `ci.name ≠ ``Eq`, the `Eq` constant is unchanged between `env` and `env'`:

```
env'.constants ``Eq = env.constants ``Eq   (since ci.name ≠ Eq)
```

So `M.modelsEq` (which gives the property for `env`) can be used directly for `env'`.

### Why the shadowing case is hard

When `ci.name = ``Eq`:

1. `addConst_fresh hadd` gives `env.constants ``Eq = none`
   (addConst only succeeds when the name is fresh)

2. `hqr : env'.QuotReady` (or `hqr_env₁`) gives `env'.constants ``Eq = some eqConst`

3. From the definition of `addConst`, `env'.constants ``Eq = some ci.toVConstant`

4. Therefore `ci.toVConstant = eqConst`

5. This means the declaration IS `Eq` — it has the same type as the built-in equality.

6. The assignment for `Eq` becomes `meaning.value [n]` (or `interp ... ci.value [n]`)

7. We must prove:
   ```
   depApp (depApp (depApp (meaning.value [n]) A) a) b = truthValue (a = b)
   ```

### The gap

`AxiomMeaning.valid` only guarantees:
```
meaning.value [n] ∈ interp κ env assignment [n] [] [] ci.type
```

When `ci.type = type_of% @Eq`, this says `meaning.value [n]` is in the
interpretation of `Eq`'s TYPE (`∀ {α} (a b : α), Prop`). It does NOT say
`meaning.value [n]` IS the canonical Eq interpretation.

`meaning.value [n]` could be ANY function of type `∀ (a b : α), Prop`.
We cannot prove it equals the specific function `fun a b => truthValue (a = b)`.

The same issue applies to defn/opaque cases: `ci.value` is some term of type
`Eq`, but we cannot prove its interpretation equals the canonical one.

### What would fix it

Strengthen `AxiomMeaning` (or add a new structure) to require that the
semantic value satisfies the `truthValue (a = b)` property:

```lean
structure AxiomMeaningWithEq (κ : ℕ → Cardinal.{u}) (env : VEnv)
    (assignment : Assignment.{u}) (ci : VConstVal) where
  value : List Nat → ZFSet.{u}
  valid : ∀ ns, ns.length = ci.uvars → value ns ∈ interp κ env assignment ns [] [] ci.type
  eq_valid : ∀ n, ∀ A ∈ ModelUniverse κ n, ∀ a ∈ A, ∀ b ∈ A,
    depApp (depApp (depApp (value [n]) A) a) b = truthValue (a = b)
```

This is an upstream change to `ModelConstruction.lean` (or a new file).

---

## Boundary Cases (ModelConstructionDebt.lean)

### 1. `model_axiom_boundary` (line 30) — INTENTIONALLY FALSE

```lean
theorem model_axiom_boundary {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} {ci : VConstVal}
    (M : ModelSetup κ env assignment) (hci : ci.toVConstant.WF env)
    (hadd : env.addConst ci.name ci.toVConstant = some env') (henv' : env'.WF) :
    ∃ assignment', ModelSetup κ env' assignment' := by
  sorry
```

**Problem**: The statement is false as written. An axiom may have an uninhabited type
(e.g., `VExpr.false`), making it impossible to construct the required
`AxiomMeaning`. The module doc already marks this as a "known-false placeholder."

**Fix**: Restrict `ci` to axioms whose types are known to be inhabited, e.g. via
`IsStandardAxiom` (which covers only `propext`, `Classical.choice`, `Quot.sound`).

---

### 2. `model_inductive_boundary` (line 39) — BLOCKED BY UPSTREAM

```lean
theorem model_inductive_boundary {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} {decl : VInductDecl}
    (M : ModelSetup κ env assignment) (hdecl : decl.WF env)
    (hadd : env.addInduct decl = some env') (henv' : env'.WF) :
    ∃ assignment', ModelSetup κ env' assignment' := by
  sorry
```

**Problem**: `VInductDecl.WF` and `VEnv.addInduct` are defined as `sorry` in
upstream `Inductive.lean`:

```lean
-- .lake/packages/lean4lean/Lean4Lean/Theory/Inductive.lean:5-7
def VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop := sorry
def VEnv.addInduct (env : VEnv) (decl : VInductDecl) : Option VEnv := sorry
```

Without these definitions, there is no way to extract well-formedness information
from `hdecl : decl.WF env` or to construct an environment extension from `hadd`.

**Fix**: Define `VInductDecl.WF` and `VEnv.addInduct` in upstream
`Inductive.lean`. Once defined, `model_inductive_boundary` becomes provable using
the inductive-type machinery (similar to how `model_addQuot_sem` works for quotients).

---

### 3. `model_quotient_boundary` (line 56) — BLOCKED BY MISSING INVARIANT

```lean
theorem model_quotient_boundary {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}}
    (M : ModelSetup κ env assignment) (hready : env.QuotReady)
    (hadd : env.addQuot = some env') (henv' : env'.WF) :
    ∃ assignment', ModelSetup κ env' assignment' := by
  sorry
```

**Problem**: The quotient mathematics is complete — `model_addQuot_sem` in
`QuotientConstruction.lean` fully proves the `ModelSetup` construction for the
`addQuot` step, including the `modelsEq` invariant. However, `model_quotient_boundary`
is a separate theorem that must work with the raw `addQuot` operation WITHOUT the
`modelsEq` information.

The current signature cannot express that `Eq` has its canonical semantic meaning
in `env'`. The `ModelSetup` for `env'` requires `modelsEq`, but the theorem's
conclusion `∃ assignment', ModelSetup κ env' assignment'` doesn't carry that
invariant.

**Fix**: Strengthen `ModelSetup` (or add a new structure) to carry the
`modelsEq` invariant, then use `model_addQuot_sem` to prove this theorem.

---

## Summary

| Sorrie | File | Blocker | Upstream Change Needed |
|--------|------|---------|----------------------|
| Eq-shadowing (axiom) | ModelConstruction.lean:235 | AxiomMeaning too weak | Strengthen AxiomMeaning |
| Eq-shadowing (defn) | ModelConstruction.lean:471 | Same as above | Same |
| Eq-shadowing (opaque) | ModelConstruction.lean:517 | Same as above | Same |
| `model_axiom_boundary` | ModelConstructionDebt.lean:30 | Statement is false | Restrict axiom predicate |
| `model_inductive_boundary` | ModelConstructionDebt.lean:39 | Upstream `sorry` | Define VInductDecl.WF/addInduct |
| `model_quotient_boundary` | ModelConstructionDebt.lean:56 | Missing invariant | Carry modelsEq through induction |
