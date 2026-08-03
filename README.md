# lean4lean-model

A Lean 4 package for model constructions over the [lean4lean](https://github.com/digama0/lean4lean)
formalization of Lean's type theory, with [mathlib](https://github.com/leanprover-community/mathlib4)
available for the mathematical side.

## Building

```sh
lake exe cache get   # mathlib oleans
lake build
```

Everything is pinned at Lean `v4.30.0`: mathlib `v4.30.0`, lean4lean `7842f38`.

Note that importing lean4lean alongside mathlib requires lean4lean's stdlib prelude
(`Lean4Lean/Std/Basic.lean`) to live in the `Lean4Lean` namespace rather than the root one --
12 of its names are also mathlib names, and the environment merge rejects duplicate constants.
That is the case on lean4lean master as of `7842f38`; consumers just need an `open Lean4Lean`.

## Target

`Lean4LeanModel/Consistency.lean` proves the final contradiction from semantic soundness for the
type theory formalized in `Lean4Lean.Theory`, assuming `ω` inaccessible cardinals -- the soundness
theorem of *The Type Theory of Lean*. Temporary declaration-model boundaries are isolated in
`Lean4LeanModel/ModelConstructionDebt.lean`.

The model is split into the following modules:

- `Lean4LeanModel.Grothendieck` proves the rank, cardinality, replacement, bounded-union, product,
  and function-graph closure properties of `V_ κ.ord` for inaccessible `κ`.
- `Lean4LeanModel.Universe` defines the proof-irrelevant proposition universe and the cumulative
  hierarchy interpreting Lean's universe levels.
- `Lean4LeanModel.DependentFunction` defines dependent function graphs, abstraction, application,
  logical quantification, and the corresponding beta, eta, and universe-closure theorems.
- `Lean4LeanModel.SetQuotient` and `Lean4LeanModel.Quotient` construct genuine quotients by the
  equivalence closure of an arbitrary relation, including proof-irrelevant `Prop` dispatch,
  soundness, lift computation, induction, and inaccessible-universe closure.
- `Lean4LeanModel.QuotientModel` connects that construction to lean4lean's exact `Quot` declaration
  and `Quot.mk` declaration, identifies the exact interpreted respect domain of `Quot.lift`, and
  isolates the invariants needed to wire the remaining quotient primitives and computation rule
  into the declaration model.
- `Lean4LeanModel.Upstream` is the audited adapter around lean4lean's currently sorried
  unique-typing and sort-inversion dependencies; CI rejects direct uses of that trust boundary
  elsewhere in the model.
- `Lean4LeanModel.Semantics` defines canonical Prop/Type and proof/data classification and the total
  structural interpretation of raw expressions.
- `Lean4LeanModel.Context` relates dependent syntactic contexts to their semantic valuations.
- `Lean4LeanModel.ModelSetup` packages the inaccessible hierarchy, well-formed environment, and
  semantic obligations for constant assignments and primitive definitional equations.
- `Lean4LeanModel.StandardAxioms` identifies the exact declarations of `propext`,
  `Classical.choice`, and `Quot.sound`, and provides a predicate-agnostic way to state that a
  declaration history contains no other axioms.
- `Lean4LeanModel.CoreRules` proves the compositional semantic universe, product, abstraction, and
  application rules used by the fundamental theorem.
- `Lean4LeanModel.Transport` proves semantic weakening, substitution, and universe-level
  instantiation.
- `Lean4LeanModel.ContextConversion` proves invariance of classifiers and interpretation under
  definitionally equal local contexts.
- `Lean4LeanModel.Fundamental` proves semantic soundness for every constructor of lean4lean's
  definitional-equality relation.
- `Lean4LeanModel.ModelConstruction` builds assignments through definitions, opaque declarations,
  and examples, assembles them along a well-formed declaration history, and exposes an axiom
  construction hook independently of the eventual allowed-axiom predicate.
- `Lean4LeanModel.ModelConstructionDebt` isolates the three remaining declaration boundaries:
  arbitrary axioms, upstream-unspecified inductives, and the standard-compatible quotient model.

The fundamental theorem and the final implication from a semantic model to consistency are
complete. Definitions, opaque declarations, and examples have a concrete assignment construction.
The present unrestricted `consistency` statement is nevertheless refutable by declaring an axiom
of `VExpr.false`; its axiom-case `sorry` is retained only for that backwards-compatible statement.
The standard-axiom path instead accepts any policy implying that each axiom is exactly `propext`,
`Classical.choice`, or `Quot.sound`, and routes those declarations through a dedicated construction
hook. That hook cannot yet be implemented because its meanings depend on the still-pending
canonical inductive interpretations; in particular, mere well-formedness does not fix the
interpretations of `Eq`, `Iff`, or `Nonempty`.
Inductive declarations are genuinely blocked by the currently sorried upstream definitions. A
genuine quotient construction is available and is proved compatible with `Quot.sound` at the
semantic-operation level. The exact `Quot` and `Quot.mk` primitive types are validated, and the
interpreted `Quot.lift` respect domain is proved equal to the truth value of its metatheoretic
respect condition under canonical equality. Completing the `addQuot` environment step requires a
history-induction motive (or stronger `ModelSetup`) carrying `ModelsEq` and `ModelsQuot`, validation
of the remaining `Quot.lift` and `Quot.ind` types, and connection of the constructed beta rule to
lean4lean's `quotDefEq`. The current `model_quotient_boundary` signature cannot provide those
invariants: `QuotReady` records only that `Eq` is declared. Thus `addQuot` remains transitively
blocked on the pending canonical inductive interpretation of `Eq`, rather than on quotient theory.
