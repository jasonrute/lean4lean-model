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

end Lean4LeanModel
