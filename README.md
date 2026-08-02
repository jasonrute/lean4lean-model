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

`Lean4LeanModel/Consistency.lean` states the goal: consistency of the type theory formalized in
`Lean4Lean.Theory`, assuming `ω` inaccessible cardinals -- the soundness theorem of *The Type
Theory of Lean*. It is `sorry`ed pending the model construction.

The first model layers are split into eight modules:

- `Lean4LeanModel.Grothendieck` proves the rank, cardinality, replacement, bounded-union, product,
  and function-graph closure properties of `V_ κ.ord` for inaccessible `κ`.
- `Lean4LeanModel.Universe` defines the proof-irrelevant proposition universe and the cumulative
  hierarchy interpreting Lean's universe levels.
- `Lean4LeanModel.DependentFunction` defines dependent function graphs, abstraction, application,
  logical quantification, and the corresponding beta, eta, and universe-closure theorems.
- `Lean4LeanModel.Upstream` is the audited adapter around lean4lean's unique-typing and sort-inversion
  results; CI rejects direct uses of that trust boundary elsewhere in the model.
- `Lean4LeanModel.Semantics` defines canonical Prop/Type and proof/data classification and the total
  structural interpretation of raw expressions.
- `Lean4LeanModel.Context` relates dependent syntactic contexts to their semantic valuations.
- `Lean4LeanModel.ModelSetup` packages the inaccessible hierarchy, well-formed environment, and
  semantic obligations for constant assignments and primitive definitional equations.
- `Lean4LeanModel.CoreRules` proves the compositional semantic universe, product, abstraction, and
  application rules used by the fundamental theorem.
