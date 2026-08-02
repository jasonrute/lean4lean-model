import Lean4LeanModel.CoreRules

/-! # Semantic weakening transport -/

namespace Lean4LeanModel

open Lean4Lean

universe u

/-- `γ'` is obtained from `γ` by inserting values at de Bruijn depth `k`. -/
def ValLiftN (n k : Nat) (γ γ' : List ZFSet.{u}) : Prop :=
  ∀ i, γ'.getD (liftVar n i k) bullet = γ.getD i bullet

theorem ValLiftN.cons (h : ValLiftN n k γ γ') (x : ZFSet.{u}) :
    ValLiftN n (k + 1) (x :: γ) (x :: γ') := by
  intro i
  cases i with
  | zero => simp [ValLiftN, liftVar]
  | succ i => simpa [ValLiftN] using h i

theorem ValLiftN.one (x : ZFSet.{u}) (γ : List ZFSet.{u}) :
    ValLiftN 1 0 γ (x :: γ) := by
  intro i
  simp [ValLiftN, liftVar, Nat.add_comm]

theorem ValLiftN.zero (ρ γ : List ZFSet.{u}) (hρ : ρ.length = n) :
    ValLiftN n 0 γ (ρ ++ γ) := by
  intro i
  rw [liftVar_base, List.getD_append_right]
  · simp [hρ]
  · simp [hρ]

private theorem onCtx_succ_lift_iff {env : VEnv} {U n k : Nat}
    {Γ Γ' : List VExpr} {A : VExpr} (henv : env.WF) (W : Ctx.LiftN n k Γ Γ')
    (hctx : OnCtx Γ' (env.IsType U) ↔ OnCtx Γ (env.IsType U)) :
    OnCtx (A.liftN n k :: Γ') (env.IsType U) ↔ OnCtx (A :: Γ) (env.IsType U) := by
  constructor
  · rintro ⟨hΓ', u, hA⟩
    exact ⟨hctx.1 hΓ', u, (Upstream.hasType_liftN_sort_iff henv hΓ' W).1 hA⟩
  · rintro ⟨hΓ, u, hA⟩
    have hΓ' := hctx.2 hΓ
    exact ⟨hΓ', u, (Upstream.hasType_liftN_sort_iff henv hΓ' W).2 hA⟩

/-- Interpretation commutes with weakening, including under binders. -/
theorem interp_liftN {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    {L : List Nat} {n k : Nat} {Γ Γ' : List VExpr} {γ γ' : List ZFSet.{u}}
    (henv : env.WF) (W : Ctx.LiftN n k Γ Γ')
    (hctx : OnCtx Γ' (env.IsType L.length) ↔ OnCtx Γ (env.IsType L.length))
    (hval : ValLiftN n k γ γ') (e : VExpr) :
    interp κ env assignment L Γ' γ' (e.liftN n k) =
      interp κ env assignment L Γ γ e := by
  induction e generalizing k Γ Γ' γ γ' with
  | bvar i => exact hval i
  | sort l => rfl
  | const c ls =>
    simp only [VExpr.liftN, interp_const]
    have hc := safeTermClass_weakN (e := .const c ls) henv W hctx
    simpa only [VExpr.liftN] using congrArg
      (fun q => if q = 0 then bullet else assignment.constVal c (ls.map (VLevel.eval L))) hc
  | app f a ihf iha =>
    simp only [VExpr.liftN, interp_app]
    rw [safeTermClass_weakN henv W hctx, ihf W hctx hval, iha W hctx hval]
  | lam A body ihA ihbody =>
    simp only [VExpr.liftN, interp_lam]
    rw [safeTermClass_weakN henv W.succ (onCtx_succ_lift_iff henv W hctx),
      ihA W hctx hval]
    apply lamValue_congr
    intro x _
    exact ihbody W.succ (onCtx_succ_lift_iff henv W hctx) (hval.cons x)
  | forallE A body ihA ihbody =>
    simp only [VExpr.liftN, interp_forallE]
    rw [safeTypeClass_weakN henv W.succ (onCtx_succ_lift_iff henv W hctx),
      ihA W hctx hval]
    apply piValue_congr
    intro x _
    exact ihbody W.succ (onCtx_succ_lift_iff henv W hctx) (hval.cons x)

theorem interp_lift {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}} {A : VExpr} (henv : env.WF)
    (hΓA : OnCtx (A :: Γ) (env.IsType L.length)) (x : ZFSet.{u}) (e : VExpr) :
    interp κ env assignment L (A :: Γ) (x :: γ) e.lift =
      interp κ env assignment L Γ γ e := by
  exact interp_liftN henv Ctx.LiftN.one
    ⟨fun h => h.1, fun _ => hΓA⟩ (ValLiftN.one x γ) e

/-- Every syntactic variable lookup is validated by a modeled context. -/
theorem ModelsCtx.lookup {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} {L : List Nat} {Γ : List VExpr}
    {γ : List ZFSet.{u}} {i : Nat} {A : VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType L.length))
    (hγ : ModelsCtx κ env assignment L Γ γ) (hL : Lookup Γ i A) :
    interp κ env assignment L Γ γ (.bvar i) ∈ interp κ env assignment L Γ γ A := by
  induction hγ generalizing i A with
  | nil => cases hL
  | @cons Γ γ B x htail hx ih =>
    cases hL with
    | zero =>
      simpa only [interp_bvar, List.getD_cons_zero, interp_lift henv hΓ x B] using hx
    | succ hL =>
      have hmem := ih hΓ.1 hL
      simpa only [interp_bvar, List.getD_cons_succ, interp_lift henv hΓ x _] using hmem

/-! ## Typed substitution -/

theorem safeTermClass_instN {env : VEnv} {U k : Nat} {Γ₀ Γ₁ Γ : List VExpr}
    {L : List Nat} {e₀ A₀ e : VExpr} (henv : env.WF)
    (hΓ₁ : OnCtx Γ₁ (env.IsType U)) (hΓ : OnCtx Γ (env.IsType U))
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType U Γ₀ e₀ A₀)
    (he : e.WF env U Γ₁) (hU : U = L.length) :
    safeTermClass env Γ L (e.inst e₀ k) = safeTermClass env Γ₁ L e := by
  subst U
  obtain ⟨A, heA⟩ := he
  obtain ⟨u, hA⟩ := heA.isType henv hΓ₁
  rw [safeTermClass_eq hΓ, safeTermClass_eq hΓ₁]
  unfold termClass
  apply congrArg classLevel
  apply propext
  rw [isProofTerm_iff_of_hasType henv hΓ₁ heA hA]
  rw [isProofTerm_iff_of_hasType henv hΓ
    (VEnv.HasType.instN henv W heA h₀) (VEnv.HasType.instN henv W hA h₀)]

theorem safeTypeClass_instN {env : VEnv} {U k : Nat} {Γ₀ Γ₁ Γ : List VExpr}
    {L : List Nat} {e₀ A₀ A : VExpr} (henv : env.WF)
    (hΓ₁ : OnCtx Γ₁ (env.IsType U)) (hΓ : OnCtx Γ (env.IsType U))
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType U Γ₀ e₀ A₀)
    (hAty : env.IsType U Γ₁ A) (hU : U = L.length) :
    safeTypeClass env Γ L (A.inst e₀ k) = safeTypeClass env Γ₁ L A := by
  subst U
  obtain ⟨u, hA⟩ := hAty
  rw [safeTypeClass_eq hΓ, safeTypeClass_eq hΓ₁]
  unfold typeClass
  apply congrArg classLevel
  apply propext
  rw [isPropType_iff_of_hasType henv hΓ₁ hA]
  rw [isPropType_iff_of_hasType henv hΓ (VEnv.HasType.instN henv W hA h₀)]

/-- Valuations related by one syntactic context instantiation. -/
inductive ValInstN (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u})
    (L : List Nat) (Γ₀ : List VExpr) (γ₀ : List ZFSet.{u}) (e₀ A₀ : VExpr) :
    {k : Nat} → {Γ₁ Γ : List VExpr} → Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ →
      List ZFSet.{u} → List ZFSet.{u} → Prop
  | zero : ValInstN κ env assignment L Γ₀ γ₀ e₀ A₀ .zero
      (interp κ env assignment L Γ₀ γ₀ e₀ :: γ₀) γ₀
  | succ {W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ} {γ₁ γ} (x : ZFSet.{u}) :
      ValInstN κ env assignment L Γ₀ γ₀ e₀ A₀ W γ₁ γ →
      ValInstN κ env assignment L Γ₀ γ₀ e₀ A₀ W.succ (x :: γ₁) (x :: γ)

theorem ValInstN.bvar {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    {L : List Nat} {Γ₀ : List VExpr} {γ₀ : List ZFSet.{u}} {e₀ A₀ : VExpr}
    {k : Nat} {Γ₁ Γ : List VExpr} {W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ}
    {γ₁ γ : List ZFSet.{u}} (h : ValInstN κ env assignment L Γ₀ γ₀ e₀ A₀ W γ₁ γ)
    (henv : env.WF) (hΓ₁ : OnCtx Γ₁ (env.IsType L.length))
    (hΓ : OnCtx Γ (env.IsType L.length))
    (i : Nat) :
    interp κ env assignment L Γ γ ((VExpr.bvar i).inst e₀ k) =
      interp κ env assignment L Γ₁ γ₁ (VExpr.bvar i) := by
  induction h generalizing i with
  | zero =>
    cases i with
    | zero => simp [VExpr.inst, VExpr.instVar]
    | succ i => simp [VExpr.inst, VExpr.instVar]
  | succ x _ ih =>
    cases i with
    | zero => simp [VExpr.inst, VExpr.instVar]
    | succ i =>
      rw [VExpr.inst, VExpr.instVar_succ, interp_lift henv hΓ x]
      simpa only [interp_bvar, List.getD_cons_succ] using ih hΓ₁.1 hΓ.1 i

/-- Interpretation commutes with substitution on well-typed raw expressions. -/
theorem interp_instN {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    {L : List Nat} {Γ₀ : List VExpr} {γ₀ : List ZFSet.{u}} {e₀ A₀ : VExpr}
    {k : Nat} {Γ₁ Γ : List VExpr} {W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ}
    {γ₁ γ : List ZFSet.{u}} (henv : env.WF)
    (hΓ₁ : OnCtx Γ₁ (env.IsType L.length)) (hΓ : OnCtx Γ (env.IsType L.length))
    (h₀ : env.HasType L.length Γ₀ e₀ A₀)
    (hval : ValInstN κ env assignment L Γ₀ γ₀ e₀ A₀ W γ₁ γ)
    (e : VExpr) (he : e.WF env L.length Γ₁) :
    interp κ env assignment L Γ γ (e.inst e₀ k) =
      interp κ env assignment L Γ₁ γ₁ e := by
  induction e generalizing k Γ₁ Γ γ₁ γ with
  | bvar i => exact hval.bvar henv hΓ₁ hΓ i
  | sort l => rfl
  | const c ls =>
    simp only [VExpr.inst, interp_const]
    have hc := safeTermClass_instN henv hΓ₁ hΓ W h₀ he rfl
    simpa only [VExpr.inst] using congrArg
      (fun q => if q = 0 then bullet else assignment.constVal c (ls.map (VLevel.eval L))) hc
  | app f a ihf iha =>
    obtain ⟨A, B, hf, ha⟩ := he.app_inv henv hΓ₁
    simp only [VExpr.inst, interp_app]
    rw [safeTermClass_instN henv hΓ₁ hΓ W h₀ ⟨_, hf⟩ rfl,
      ihf hΓ₁ hΓ hval ⟨_, hf⟩,
      iha hΓ₁ hΓ hval ⟨_, ha⟩]
  | lam C body ihC ihbody =>
    obtain ⟨hC, hbody⟩ := he.lam_inv henv hΓ₁
    have hCwf : C.WF env L.length Γ₁ := by
      obtain ⟨u, hu⟩ := hC
      exact ⟨.sort u, hu⟩
    have hCi := VEnv.IsType.instN henv W hC h₀
    have hΓ₁C : OnCtx (C :: Γ₁) (env.IsType L.length) := ⟨hΓ₁, hC⟩
    have hΓCi : OnCtx (C.inst e₀ k :: Γ) (env.IsType L.length) := ⟨hΓ, hCi⟩
    simp only [VExpr.inst, interp_lam]
    rw [safeTermClass_instN henv hΓ₁C hΓCi W.succ h₀ hbody rfl,
      ihC hΓ₁ hΓ hval hCwf]
    apply lamValue_congr
    intro x _
    exact ihbody hΓ₁C hΓCi (hval.succ x) hbody
  | forallE C body ihC ihbody =>
    obtain ⟨V, hfor⟩ := he
    obtain ⟨hC, hbody⟩ := VEnv.HasType.forallE_inv henv hfor
    have hCwf : C.WF env L.length Γ₁ := by
      obtain ⟨u, hu⟩ := hC
      exact ⟨.sort u, hu⟩
    have hbodywf : body.WF env L.length (C :: Γ₁) := by
      obtain ⟨v, hv⟩ := hbody
      exact ⟨.sort v, hv⟩
    have hCi := VEnv.IsType.instN henv W hC h₀
    have hΓ₁C : OnCtx (C :: Γ₁) (env.IsType L.length) := ⟨hΓ₁, hC⟩
    have hΓCi : OnCtx (C.inst e₀ k :: Γ) (env.IsType L.length) := ⟨hΓ, hCi⟩
    simp only [VExpr.inst, interp_forallE]
    rw [safeTypeClass_instN henv hΓ₁C hΓCi W.succ h₀ hbody rfl,
      ihC hΓ₁ hΓ hval hCwf]
    apply piValue_congr
    intro x _
    exact ihbody hΓ₁C hΓCi (hval.succ x) hbodywf

theorem interp_inst {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}} {a A e : VExpr}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType L.length))
    (ha : env.HasType L.length Γ a A) (hA : env.IsType L.length Γ A)
    (he : e.WF env L.length (A :: Γ)) :
    interp κ env assignment L Γ γ (e.inst a) =
      interp κ env assignment L (A :: Γ)
        (interp κ env assignment L Γ γ a :: γ) e := by
  have hΓA : OnCtx (A :: Γ) (env.IsType L.length) := ⟨hΓ, hA⟩
  exact interp_instN (W := Ctx.InstN.zero) henv hΓA hΓ ha ValInstN.zero e he

end Lean4LeanModel
