import Lean4LeanModel.Quotient
import Lean4LeanModel.ModelSetup
import Lean4Lean.Theory.Typing.QuotLemmas

/-!
# Semantic meanings of Lean's quotient primitives

This module begins the bridge from the representation-independent quotient operations to the
primitive declarations installed by `VEnv.addQuot`: it validates the exact `Quot` type-former
declaration and states the canonical `Eq` and quotient-assignment invariants required by the
remaining constants and computation rule.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

/-- The semantic proposition obtained by applying the assigned interpretation of `Eq`. -/
noncomputable def assignedEqValue (assignment : Assignment.{u}) (n : Nat)
    (A a b : ZFSet.{u}) : ZFSet.{u} :=
  depApp (depApp (depApp (assignment.constVal ``Eq [n]) A) a) b

/-- The precise invariant about the canonical `Eq` interpretation needed by genuine quotients.
The future inductive construction must establish this when it installs `Eq`; ordinary declaration
extensions then preserve it. -/
def Assignment.ModelsEq (κ : ℕ → Cardinal.{u}) (assignment : Assignment.{u}) : Prop :=
  ∀ n, ∀ A ∈ ModelUniverse κ n, ∀ a ∈ A, ∀ b ∈ A,
    assignedEqValue assignment n A a b = truthValue (a = b)

theorem Assignment.ModelsEq.congr {κ : ℕ → Cardinal.{u}}
    {assignment assignment' : Assignment.{u}} (hEq : assignment.ModelsEq κ)
    (h : ∀ ns, assignment'.constVal ``Eq ns = assignment.constVal ``Eq ns) :
    assignment'.ModelsEq κ := by
  intro n A hA a ha b hb
  simpa [assignedEqValue, h [n]] using hEq n A hA a ha b hb

/-- The assigned quotient type former and constructor are the genuine values constructed in
`Quotient`. This is the additional invariant needed when validating a later `Quot.sound` axiom. -/
def Assignment.ModelsQuot (κ : ℕ → Cardinal.{u}) (assignment : Assignment.{u}) : Prop :=
  (∀ n, assignment.constVal ``Quot [n] = quotTypeValue κ n) ∧
  (∀ n, assignment.constVal ``Quot.mk [n] = quotMkConstValue κ n)

theorem Assignment.ModelsQuot.congr {κ : ℕ → Cardinal.{u}}
    {assignment assignment' : Assignment.{u}} (hQuot : assignment.ModelsQuot κ)
    (h : ∀ c ns, c = ``Quot ∨ c = ``Quot.mk →
      assignment'.constVal c ns = assignment.constVal c ns) :
    assignment'.ModelsQuot κ := by
  constructor
  · intro n
    rw [h ``Quot [n] (Or.inl rfl)]
    exact hQuot.1 n
  · intro n
    rw [h ``Quot.mk [n] (Or.inr rfl)]
    exact hQuot.2 n

/-- Canonical equality turns the interpreted respect premise of `Quot.lift` into the
metatheoretic equality condition used by `quotLiftConstValue`. -/
theorem quotientRespects_of_modelsEq {κ : ℕ → Cardinal.{u}}
    {assignment : Assignment.{u}} (hEq : assignment.ModelsEq κ)
    {m : Nat} {A B r f : ZFSet.{u}} (hB : B ∈ ModelUniverse κ m)
    (hf : f ∈ piValue m A (fun _ => B))
    (h : ∀ a ∈ A, ∀ b ∈ A, relationOfGraph r a b →
      bullet ∈ assignedEqValue assignment m B (appValue m f a) (appValue m f b)) :
    QuotientRespects m A (relationOfGraph r) f := by
  intro a ha b hb hab
  have hfa : appValue m f a ∈ B := appValue_mem hf ha
  have hfb : appValue m f b ∈ B := appValue_mem hf hb
  have heq := h a ha b hb hab
  rw [hEq m B hB (appValue m f a) hfa (appValue m f b) hfb,
    bullet_mem_truthValue] at heq
  exact heq

/-- `Quot.sound` is valid for the genuine quotient whenever `Eq` has its canonical meaning. -/
theorem quotSound_semantic {κ : ℕ → Cardinal.{u}} {assignment : Assignment.{u}}
    (hi : ∀ n, (κ n).IsInaccessible) (hEq : assignment.ModelsEq κ)
    {n : Nat} {A r a b : ZFSet.{u}}
    (hA : A ∈ ModelUniverse κ n) (ha : a ∈ A) (hb : b ∈ A)
    (hab : relationOfGraph r a b) :
    bullet ∈ assignedEqValue assignment n (quotValue n A (relationOfGraph r))
      (quotMkValue n A (relationOfGraph r) a)
      (quotMkValue n A (relationOfGraph r) b) := by
  rw [hEq n (quotValue n A (relationOfGraph r))
    (quotValue_mem_ModelUniverse hi hA)
    (quotMkValue n A (relationOfGraph r) a) (quotMkValue_mem ha)
    (quotMkValue n A (relationOfGraph r) b) (quotMkValue_mem hb)]
  rw [bullet_mem_truthValue]
  exact quotMkValue_sound ha hb hab

private theorem safeTypeClass_forallE_eq {env : VEnv} {L : List Nat} {Γ : List VExpr}
    {A B : VExpr} (henv : env.WF) (hΓ : OnCtx Γ (env.IsType L.length))
    (hA : env.IsType L.length Γ A) (hB : env.IsType L.length (A :: Γ) B) :
    safeTypeClass env Γ L (.forallE A B) = safeTypeClass env (A :: Γ) L B := by
  obtain ⟨u, hA⟩ := hA
  obtain ⟨v, hB⟩ := hB
  have hΓA : OnCtx (A :: Γ) (env.IsType L.length) := ⟨hΓ, ⟨u, hA⟩⟩
  calc
    safeTypeClass env Γ L (.forallE A B) = typeClass env Γ L (.forallE A B) :=
      safeTypeClass_eq hΓ
    _ = typeClass env (A :: Γ) L B := typeClass_forallE henv hΓ hA hB
    _ = safeTypeClass env (A :: Γ) L B := (safeTypeClass_eq hΓA).symm

private theorem safeTypeClass_sort_ne_zero {env : VEnv} {L : List Nat} {Γ : List VExpr}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType L.length)) (l : VLevel)
    (hl : l.WF L.length) : safeTypeClass env Γ L (.sort l) ≠ 0 := by
  rw [Ne, safeTypeClass_eq hΓ, typeClass_eq_zero_iff_of_hasType henv hΓ (.sort hl)]
  simp [VLevel.eval]

theorem quotConstValue_valid {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} (henv : env.WF)
    (hi : ∀ n, (κ n).IsInaccessible) (n : Nat) :
    quotTypeValue κ n ∈ interp κ env assignment [n] [] [] quotConst.type := by
  let α : VExpr := .sort (.param 0)
  let rel : VExpr := .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))
  have hα : env.IsType 1 [] α := by
    refine ⟨.succ (.param 0), ?_⟩
    exact .sort (by decide)
  have hΓα : OnCtx [α] (env.IsType 1) := ⟨trivial, hα⟩
  have hrel : env.IsType 1 [α] rel := by
    refine ⟨.imax (.param 0) (.imax (.param 0) (.succ .zero)), ?_⟩
    simp only [rel]
    apply VEnv.HasType.forallE
    · type_tac
    · apply VEnv.HasType.forallE
      · type_tac
      · exact .sort trivial
  have hΓrel : OnCtx [rel, α] (env.IsType 1) := ⟨hΓα, hrel⟩
  have hα' : env.IsType 1 [rel, α] α := by
    exact ⟨.succ (.param 0), .sort (by decide)⟩
  have hb0 : env.IsType 1 [α] (.bvar 0) := by
    exact ⟨.param 0, by type_tac⟩
  have hΓb0 : OnCtx [.bvar 0, α] (env.IsType 1) := ⟨hΓα, hb0⟩
  have hb1 : env.IsType 1 [.bvar 0, α] (.bvar 1) := by
    exact ⟨.param 0, by type_tac⟩
  have hΓb1 : OnCtx [.bvar 1, .bvar 0, α] (env.IsType 1) := ⟨hΓb0, hb1⟩
  have hrelBody : env.IsType 1 [.bvar 1, .bvar 0, α] (.sort .zero) := by
    exact ⟨.succ .zero, .sort trivial⟩
  have hcResult : safeTypeClass env [rel, α] [n] α ≠ 0 := by
    exact safeTypeClass_sort_ne_zero henv hΓrel (.param 0) Nat.zero_lt_one
  have hcRelInner :
      safeTypeClass env [.bvar 1, .bvar 0, α] [n] (.sort .zero) ≠ 0 := by
    exact safeTypeClass_sort_ne_zero henv hΓb1 .zero trivial
  have hcRelOuter :
      safeTypeClass env [.bvar 0, α] [n] (.forallE (.bvar 1) (.sort .zero)) ≠ 0 := by
    rw [safeTypeClass_forallE_eq (L := [n]) (Γ := [.bvar 0, α])
      henv hΓb0 hb1 hrelBody]
    exact hcRelInner
  have hcOuter : safeTypeClass env [α] [n] (.forallE rel α) ≠ 0 := by
    rw [safeTypeClass_forallE_eq (L := [n]) (Γ := [α])
      henv hΓα hrel hα']
    exact hcResult
  change quotTypeValue κ n ∈
    interp κ env assignment [n] [] [] (.forallE α (.forallE rel α))
  simp only [interp_forallE, piValue, hcOuter, hcResult, if_false]
  simp only [α, rel, interp_sort, interp_forallE, interp_bvar, piValue,
    hcRelOuter, hcRelInner, if_false, List.getD_cons_zero, List.getD_cons_succ]
  change quotTypeValue κ n ∈ depFuns (ModelUniverse κ n) fun A =>
    depFuns (relationSpace A) fun _ => ModelUniverse κ n
  exact quotTypeValue_mem hi n

end Lean4LeanModel
