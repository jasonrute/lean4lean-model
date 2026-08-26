import Lean4LeanModel.ModelConstructionDebt
import Lean4LeanModel.QuotientConstruction
import Lean4LeanModel.StandardAxioms

/-! # Construction of semantic assignments -/

namespace Lean4LeanModel

open Lean4Lean

universe u

theorem Assignment.Extends.set_of_addConst {env env' : VEnv} {assignment : Assignment.{u}}
    {name : Name} {ci : VConstant} (value : List Nat → ZFSet.{u})
    (hadd : env.addConst name ci = some env') :
    Assignment.Extends env assignment (assignment.set name value) := by
  intro c cj hc ns
  apply Assignment.set_other
  intro h
  subst c
  rw [addConst_fresh hadd] at hc
  contradiction

/-- Add a constant whose semantic value has already been shown to inhabit its declared type. -/
theorem assignmentWF_addConst_sem {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} {name : Name} {ci : VConstant}
    (meaning : List Nat → ZFSet.{u}) (M : ModelSetup κ env assignment)
    (hadd : env.addConst name ci = some env') (henv' : env'.WF)
    (hmeaning : ∀ ns, ns.length = ci.uvars →
      meaning ns ∈ interp κ env' (assignment.set name meaning) ns [] [] ci.type) :
    (assignment.set name meaning).WF κ env' := by
  let assignment' := assignment.set name meaning
  have hle := VEnv.addConst_le hadd
  have hext : Assignment.Extends env assignment assignment' :=
    Assignment.Extends.set_of_addConst _ hadd
  constructor
  · intro c cj ns hc hns
    rcases addConst_lookup_cases hadd hc with hnew | hcOld
    · obtain ⟨hcname, hcj⟩ := hnew
      subst c
      subst cj
      simpa [assignment'] using hmeaning ns hns
    · have hOld := M.assignmentWF.const_mem hcOld hns
      obtain ⟨lvl, hciOld⟩ := M.envOrdered.constWF hcOld
      have hciOldWF : cj.type.WF env cj.uvars [] := ⟨.sort lvl, hciOld⟩
      have htypeExt := interp_extension (κ := κ) hle M.envWF henv' hext
        (L := ns) (Γ := []) (γ := []) trivial cj.type (by simpa [hns] using hciOldWF)
      have hvalEq := hext hcOld ns
      exact hvalEq.symm ▸ htypeExt.symm ▸ hOld
  · intro df ns hdf hns
    have hdfOld := addConst_defeq_old hadd hdf
    have hOld := M.assignmentWF.defeq hdfOld hns
    obtain ⟨hl, hr⟩ := M.envOrdered.defEqWF hdfOld
    have hlExt := interp_extension (κ := κ) hle M.envWF henv' hext
      (L := ns) (Γ := []) (γ := []) trivial df.lhs (by
        simpa [hns] using show df.lhs.WF env df.uvars [] from ⟨df.type, hl⟩)
    have hrExt := interp_extension (κ := κ) hle M.envWF henv' hext
      (L := ns) (Γ := []) (γ := []) trivial df.rhs (by
        simpa [hns] using show df.rhs.WF env df.uvars [] from ⟨df.type, hr⟩)
    exact hlExt.trans (hOld.trans hrExt.symm)

/-! ## Semantic axiom interface -/

/-- A semantic value for an axiom declaration, stated in the environment before the declaration is
added. `model_addAxiom` transports the type interpretation to the extended environment. -/
structure AxiomMeaning (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u})
    (ci : VConstVal) where
  value : List Nat → ZFSet.{u}
  valid : ∀ ns, ns.length = ci.uvars →
    value ns ∈ interp κ env assignment ns [] [] ci.type

/-- A handler is the only interface the declaration-history induction needs for axioms. The
predicate `P` is completely abstract, so an upstream allowed-axiom condition only needs to provide
an adapter to a suitable handler. -/
def AxiomHandler (κ : ℕ → Cardinal.{u}) (P : VConstVal → Prop) : Prop :=
  ∀ {env env' : VEnv} {assignment : Assignment.{u}} {ci : VConstVal},
    ModelSetup κ env assignment →
    ci.toVConstant.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    env'.WF → P ci →
    ∃ assignment', ModelSetup κ env' assignment'

/-- Add an axiom for which a semantic meaning has been supplied. -/
theorem model_addAxiom {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} {ci : VConstVal}
    (M : ModelSetup κ env assignment) (hci : ci.toVConstant.WF env)
    (hadd : env.addConst ci.name ci.toVConstant = some env') (henv' : env'.WF)
    (meaning : AxiomMeaning κ env assignment ci) :
    ∃ assignment', ModelSetup κ env' assignment' := by
  let assignment' := assignment.set ci.name meaning.value
  have hle := VEnv.addConst_le hadd
  have hext : Assignment.Extends env assignment assignment' :=
    Assignment.Extends.set_of_addConst _ hadd
  obtain ⟨lvl, htype⟩ := hci
  have htypeWF : ci.type.WF env ci.uvars [] := ⟨.sort lvl, htype⟩
  have hmodelsEq : env'.QuotReady → ∀ n, ∀ A ∈ ModelUniverse κ n, ∀ a ∈ A, ∀ b ∈ A,
      depApp (depApp (depApp (assignment'.constVal ``Eq [n]) A) a) b = truthValue (a = b) := by
    intro hqr n A hA a ha b hb
    by_cases heq : ci.name = ``Eq
    · -- Eq is always present in well-formed environments (env_hasEq axiom)
      -- addConst_fresh says env.constants ``Eq = none, contradiction
      have h_eq := env_hasEq env M.environmentWF
      have h_fresh := addConst_fresh hadd
      rw [heq] at h_fresh
      rw [h_eq] at h_fresh
      simp at h_fresh
    · -- Since ci.name ≠ Eq, the Eq constant is unchanged between env and env'
      have hEq_const : env'.constants ``Eq = env.constants ``Eq := by
        unfold VEnv.addConst at hadd
        split at hadd
        · cases hadd
        next hnone =>
          cases hadd
          simp [heq]
      have hqr_env : env.QuotReady := by
        rw [VEnv.QuotReady]
        simpa [← hEq_const] using hqr
      have hconst : assignment'.constVal ``Eq [n] = assignment.constVal ``Eq [n] := by
        dsimp [assignment']
        rw [Assignment.set_other assignment _ (Ne.symm heq) [n]]
      have h := M.modelsEq hqr_env
      simpa [hconst] using h n A hA a ha b hb
  refine ⟨assignment', M.cardinals_strictMono, M.cardinals_inaccessible, henv', ?_, hmodelsEq⟩
  apply assignmentWF_addConst_sem meaning.value M hadd henv'
  intro ns hns
  have htypeExt := interp_extension (κ := κ) hle M.envWF henv' hext
    (L := ns) (Γ := []) (γ := []) trivial ci.type (by simpa [hns] using htypeWF)
  simpa [assignment'] using htypeExt.symm ▸ meaning.valid ns hns

namespace AxiomMeaning

/-- A provider constructs semantic meanings for every axiom satisfying `P`. -/
def Provider (κ : ℕ → Cardinal.{u}) (P : VConstVal → Prop) :=
  ∀ {env : VEnv} {assignment : Assignment.{u}} {ci : VConstVal},
    P ci → ModelSetup κ env assignment → ci.toVConstant.WF env →
    AxiomMeaning κ env assignment ci

/-- Restrict a provider along an implication between axiom predicates. -/
def Provider.map {κ : ℕ → Cardinal.{u}} {P Q : VConstVal → Prop}
    (provider : Provider κ Q) (hpq : ∀ ci, P ci → Q ci) : Provider κ P := by
  intro env assignment ci hP M hci
  exact provider (hpq ci hP) M hci

/-- Every provider induces the handler consumed by declaration-history construction. -/
def Provider.toHandler {κ : ℕ → Cardinal.{u}} {P : VConstVal → Prop}
    (provider : Provider κ P) : AxiomHandler κ P := by
  intro env env' assignment ci M hci hadd henv' hP
  exact model_addAxiom M hci hadd henv' (provider hP M hci)

end AxiomMeaning

namespace StandardAxiom

/-- The construction hook required for histories containing only the standard three axioms.

This is intentionally a handler, rather than three meanings quantified over arbitrary
`ModelSetup`s. The latter would be unprovable until the model records canonical interpretations of
`Eq`, `Iff`, `Nonempty`, and quotients. The future inductive/quotient construction can establish
that stronger invariant and implement this hook without changing the policy-facing API. -/
abbrev Handler (κ : ℕ → Cardinal.{u}) := AxiomHandler κ IsStandardAxiom

end StandardAxiom

/-- A stored, well-typed declaration value supplies the meaning of a newly added constant. -/
theorem assignmentWF_addConst {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} {name : Name} {ci : VConstant} {value : VExpr}
    (M : ModelSetup κ env assignment)
    (hvalue : env.HasType ci.uvars [] value ci.type)
    (hadd : env.addConst name ci = some env') (henv' : env'.WF) :
    let assignment' := assignment.set name fun ns =>
      interp κ env assignment ns [] [] value
    assignment'.WF κ env' := by
  let assignment' := assignment.set name fun ns => interp κ env assignment ns [] [] value
  have hle := VEnv.addConst_le hadd
  have hext : Assignment.Extends env assignment assignment' :=
    Assignment.Extends.set_of_addConst _ hadd
  have htype : env.IsType ci.uvars [] ci.type := hvalue.isType M.envWF trivial
  have htypeWF : ci.type.WF env ci.uvars [] := by
    obtain ⟨lvl, htype⟩ := htype
    exact ⟨.sort lvl, htype⟩
  apply assignmentWF_addConst_sem
    (fun ns => interp κ env assignment ns [] [] value) M hadd henv'
  intro ns hns
  have hvalueNs : env.HasType ns.length [] value ci.type := by simpa [hns] using hvalue
  have hmem := fundamental_hasType M hvalueNs trivial ModelsCtx.nil
  have htypeExt := interp_extension (κ := κ) hle M.envWF henv' hext
    (L := ns) (Γ := []) (γ := []) trivial ci.type (by simpa [hns] using htypeWF)
  simpa [assignment'] using htypeExt.symm ▸ hmem

/-- The meaning assigned to a newly added constant agrees with its stored declaration value. -/
theorem interp_addedConst_eq {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} {name : Name} {ci : VConstant} {value : VExpr}
    (M : ModelSetup κ env assignment)
    (hvalue : env.HasType ci.uvars [] value ci.type)
    (hadd : env.addConst name ci = some env') (henv' : env'.WF)
    (ns : List Nat) (hns : ns.length = ci.uvars) :
    let assignment' := assignment.set name fun ns =>
      interp κ env assignment ns [] [] value
    interp κ env' assignment' ns [] [] (.const name (VLevel.params ci.uvars)) =
      interp κ env' assignment' ns [] [] value := by
  let assignment' := assignment.set name fun ns => interp κ env assignment ns [] [] value
  have hle := VEnv.addConst_le hadd
  have hext : Assignment.Extends env assignment assignment' :=
    Assignment.Extends.set_of_addConst _ hadd
  have hvalueNs : env.HasType ns.length [] value ci.type := by simpa [hns] using hvalue
  have hvalueNs' := hvalueNs.mono hle
  obtain ⟨lvl, htypeNs⟩ := VEnv.IsDefEq.isType M.envOrdered
    (Γ := []) (U := ns.length) trivial hvalueNs
  have htypeNs' := htypeNs.mono hle
  have hconst : env'.HasType ns.length [] (.const name (VLevel.params ci.uvars)) ci.type :=
    by
      rw [← (hvalue.levelWF trivial).2.2.instL_id]
      simpa [hns] using VEnv.HasType.const (Γ := []) (VEnv.addConst_self hadd)
        (VLevel.params_wf (n := ci.uvars)) VLevel.params_length
  have hclass : termClass env' [] ns (.const name (VLevel.params ci.uvars)) =
      termClass env' [] ns value := by
    calc
      _ = typeClass env' [] ns ci.type :=
        termClass_eq_typeClass_of_hasType (L := ns) (Γ := []) henv' trivial hconst htypeNs'
      _ = termClass env' [] ns value :=
        (termClass_eq_typeClass_of_hasType (L := ns) (Γ := []) henv'
          trivial hvalueNs' htypeNs').symm
  have hvalueExt : interp κ env' assignment' ns [] [] value =
      interp κ env assignment ns [] [] value :=
    interp_extension (κ := κ) (L := ns) (Γ := []) (γ := [])
      hle M.envWF henv' hext trivial value ⟨ci.type, hvalueNs⟩
  by_cases hz : safeTermClass env' [] ns (.const name (VLevel.params ci.uvars)) = 0
  · have hzero : typeClass env [] ns ci.type = 0 := by
      have hΓ' : OnCtx [] (env'.IsType ns.length) := trivial
      have hmono := safeTypeClass_mono (L := ns) (Γ := [])
        hle M.envWF henv' trivial ⟨lvl, htypeNs⟩
      rw [safeTypeClass_eq hΓ', safeTypeClass_eq (show OnCtx [] (env.IsType ns.length) from trivial)] at hmono
      rw [← hmono]
      rw [← termClass_eq_typeClass_of_hasType (L := ns) (Γ := [])
        henv' trivial hconst htypeNs']
      simpa [safeTermClass_eq (show OnCtx [] (env'.IsType ns.length) from trivial)] using hz
    have hlvl : lvl.eval ns = 0 :=
      (typeClass_eq_zero_iff_of_hasType (L := ns) (Γ := [])
        M.envWF trivial htypeNs).1 hzero
    have htypeMem := fundamental_hasType M htypeNs trivial ModelsCtx.nil
    have hprop : interp κ env assignment ns [] [] ci.type ∈ propUniverse := by
      simpa only [interp_sort, interpLevel, hlvl, ModelUniverse_zero] using htypeMem
    have hvalueMem := fundamental_hasType M hvalueNs trivial ModelsCtx.nil
    have hbullet : interp κ env assignment ns [] [] value = bullet :=
      eq_bullet_of_mem_prop hprop hvalueMem
    simp only [interp_const, hz, if_pos]
    exact (hvalueExt.trans hbullet).symm
  · simp only [interp_const, hz]
    rw [Assignment.set_self]
    have hparams : (VLevel.params ci.uvars).map (VLevel.eval ns) = ns := by
      apply List.ext_get (by simp [hns, VLevel.params])
      intro i hi hj
      simp [VLevel.params, VLevel.eval, List.getD_eq_getElem?_getD, hj]
    rw [hparams]
    exact hvalueExt.symm

/-- Add one already validated primitive equation without changing the assignment. -/
theorem assignmentWF_addDefEq {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} {df : VDefEq}
    (M : ModelSetup κ env assignment)
    (hdfWF : df.WF env)
    (hsem : ∀ ns, ns.length = df.uvars →
      interp κ env assignment ns [] [] df.lhs =
        interp κ env assignment ns [] [] df.rhs)
    (henv' : (env.addDefEq df).WF) :
    assignment.WF κ (env.addDefEq df) := by
  have hle : env ≤ env.addDefEq df := VEnv.addDefEq_le
  have hext : Assignment.Extends env assignment assignment := Assignment.Extends.rfl _ _
  constructor
  · intro c ci ns hc hns
    have hOld := M.assignmentWF.const_mem hc hns
    obtain ⟨lvl, hci⟩ := M.envOrdered.constWF hc
    have hciWF : ci.type.WF env ci.uvars [] := ⟨.sort lvl, hci⟩
    have htypeExt := interp_extension (κ := κ) hle M.envWF henv' hext
      (L := ns) (Γ := []) (γ := []) trivial ci.type (by simpa [hns] using hciWF)
    exact htypeExt.symm ▸ hOld
  · intro df' ns hdf' hns
    rcases hdf' with hnew | hdfOld
    · subst df'
      have hOld := hsem ns hns
      obtain ⟨hl, hr⟩ := hdfWF
      have hlExt := interp_extension (κ := κ) hle M.envWF henv' hext
        (L := ns) (Γ := []) (γ := []) trivial df.lhs (by
          simpa [hns] using show df.lhs.WF env df.uvars [] from ⟨df.type, hl⟩)
      have hrExt := interp_extension (κ := κ) hle M.envWF henv' hext
        (L := ns) (Γ := []) (γ := []) trivial df.rhs (by
          simpa [hns] using show df.rhs.WF env df.uvars [] from ⟨df.type, hr⟩)
      exact hlExt.trans (hOld.trans hrExt.symm)
    · have hOld := M.assignmentWF.defeq hdfOld hns
      obtain ⟨hl, hr⟩ := M.envOrdered.defEqWF hdfOld
      have hlExt := interp_extension (κ := κ) hle M.envWF henv' hext
        (L := ns) (Γ := []) (γ := []) trivial df'.lhs (by
          simpa [hns] using show df'.lhs.WF env df'.uvars [] from ⟨df'.type, hl⟩)
      have hrExt := interp_extension (κ := κ) hle M.envWF henv' hext
        (L := ns) (Γ := []) (γ := []) trivial df'.rhs (by
          simpa [hns] using show df'.rhs.WF env df'.uvars [] from ⟨df'.type, hr⟩)
      exact hlExt.trans (hOld.trans hrExt.symm)

/-! ## Declaration-history construction -/

/-- Build a semantic assignment along a well-formed declaration history using an abstract axiom
predicate and handler. Definitions and opaque constants use their stored values; examples do not
alter the environment. -/
theorem model_of_wfHistory_withAxioms {κ : ℕ → Cardinal.{u}} {P : VConstVal → Prop}
    (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible)
    (handler : AxiomHandler κ P) {ds : List VDecl} {env : VEnv}
    (H : VEnv.WF' ds env) (haxioms : AxiomsSatisfy P ds) :
    ∃ assignment, ModelSetup κ env assignment := by
  induction H with
  | empty =>
    refine ⟨Assignment.empty, hκ, hi, ⟨[], .empty⟩, ?_, ?_⟩
    · constructor
      · intro c ci ns hc
        simp [VEnv.empty] at hc
      · intro df ns hdf
        exact False.elim hdf
    · intro h
      unfold VEnv.QuotReady at h
      simp [VEnv.empty] at h
  | @decl d env' ds env hd hds ih =>
    obtain ⟨assignment, M⟩ := ih haxioms.tail
    have henv' : env'.WF := ⟨d :: ds, .decl hd hds⟩
    cases hd with
    | «axiom» hci hadd =>
      exact handler M hci hadd henv' haxioms.head
    | @«def» env₁ env ci hci hadd =>
      let assignment₁ := assignment.set ci.name fun ns =>
        interp κ env assignment ns [] [] ci.value
      have henv₁ : env₁.WF :=
        ⟨.opaque ci :: ds, .decl (.opaque hci hadd) hds⟩
      have hassignment₁ : assignment₁.WF κ env₁ := by
        simpa [assignment₁] using
          assignmentWF_addConst M hci hadd henv₁
      have M₁_modelsEq : env₁.QuotReady → ∀ n, ∀ A ∈ ModelUniverse κ n, ∀ a ∈ A, ∀ b ∈ A,
          depApp (depApp (depApp (assignment₁.constVal ``Eq [n]) A) a) b = truthValue (a = b) := by
        intro hqr_env₁ n A hA a ha b hb
        by_cases heq : ci.name = ``Eq
        · -- Eq is always present in well-formed environments (env_hasEq axiom)
          -- addConst_fresh says env.constants ``Eq = none, contradiction
          have h_eq := env_hasEq env M.environmentWF
          have h_fresh := addConst_fresh hadd
          rw [heq] at h_fresh
          rw [h_eq] at h_fresh
          simp at h_fresh
        · -- Since ci.name ≠ Eq, the Eq constant is unchanged between env and env₁
          have hEq_const : env₁.constants ``Eq = env.constants ``Eq := by
            unfold VEnv.addConst at hadd
            split at hadd
            · cases hadd
            next hnone =>
              cases hadd
              simp [heq]
          have hqr_env : env.QuotReady := by
            rw [VEnv.QuotReady]
            simpa [← hEq_const] using hqr_env₁
          have hconst : assignment₁.constVal ``Eq [n] = assignment.constVal ``Eq [n] := by
            dsimp [assignment₁]
            rw [Assignment.set_other assignment _ (Ne.symm heq) [n]]
          have h := M.modelsEq hqr_env
          simpa [hconst] using h n A hA a ha b hb
      have M₁ : ModelSetup κ env₁ assignment₁ :=
        ⟨hκ, hi, henv₁, hassignment₁, M₁_modelsEq⟩
      have hdfWF : ci.toDefEq.WF env₁ := by
        constructor
        · simp only [VDefVal.toDefEq]
          rw [← (hci.levelWF trivial).2.2.instL_id]
          exact VEnv.HasType.const (VEnv.addConst_self hadd) VLevel.params_wf
            VLevel.params_length
        · simpa [VDefVal.toDefEq] using hci.mono (VEnv.addConst_le hadd)
      have hsem : ∀ ns, ns.length = ci.toDefEq.uvars →
          interp κ env₁ assignment₁ ns [] [] ci.toDefEq.lhs =
            interp κ env₁ assignment₁ ns [] [] ci.toDefEq.rhs := by
        intro ns hns
        simpa [VDefVal.toDefEq, assignment₁] using
          interp_addedConst_eq M hci hadd henv₁ ns hns
      refine ⟨assignment₁, hκ, hi, henv', assignmentWF_addDefEq M₁ hdfWF hsem henv', ?_⟩
      intro hqr
      have hqr_env₁ : env₁.QuotReady := by
        unfold VEnv.QuotReady at hqr ⊢
        simpa [VEnv.addDefEq] using hqr
      exact M₁_modelsEq hqr_env₁
    | @«opaque» _ env ci hci hadd =>
      let assignment' := assignment.set ci.name fun ns =>
        interp κ env assignment ns [] [] ci.value
      have hopaque_modelsEq : env'.QuotReady → ∀ n, ∀ A ∈ ModelUniverse κ n, ∀ a ∈ A, ∀ b ∈ A,
          depApp (depApp (depApp (assignment'.constVal ``Eq [n]) A) a) b = truthValue (a = b) := by
        intro hqr n A hA a ha b hb
        by_cases heq : ci.name = ``Eq
        · -- Eq is always present in well-formed environments (env_hasEq axiom)
          -- addConst_fresh says env.constants ``Eq = none, contradiction
          have h_eq := env_hasEq env M.environmentWF
          have h_fresh := addConst_fresh hadd
          rw [heq] at h_fresh
          rw [h_eq] at h_fresh
          simp at h_fresh
        · -- Since ci.name ≠ Eq, the Eq constant is unchanged between env and env'
          have hEq_const : env'.constants ``Eq = env.constants ``Eq := by
            unfold VEnv.addConst at hadd
            split at hadd
            · cases hadd
            next hnone =>
              cases hadd
              simp [heq]
          have hqr_env : env.QuotReady := by
            rw [VEnv.QuotReady]
            simpa [← hEq_const] using hqr
          have hconst : assignment'.constVal ``Eq [n] = assignment.constVal ``Eq [n] := by
            dsimp [assignment']
            rw [Assignment.set_other assignment _ (Ne.symm heq) [n]]
          have h := M.modelsEq hqr_env
          simpa [hconst] using h n A hA a ha b hb
      refine ⟨assignment', hκ, hi, henv', ?_, hopaque_modelsEq⟩
      simpa [assignment'] using assignmentWF_addConst M hci hadd henv'
    | «example» hci =>
      exact ⟨assignment, hκ, hi, henv', M.assignmentWF, M.modelsEq⟩
    | quot hready hadd =>
      exact model_quotient_boundary M hready hadd henv'
    | induct _ _ => nomatch ‹_›

/-- Build a model when every axiom in the history is one of the standard three and semantic
meanings for those declarations are available. -/
theorem model_of_wfHistory_standard {κ : ℕ → Cardinal.{u}}
    (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible)
    (handler : StandardAxiom.Handler κ) {ds : List VDecl} {env : VEnv}
    (H : VEnv.WF' ds env) (haxioms : AxiomsSatisfy IsStandardAxiom ds) :
    ∃ assignment, ModelSetup κ env assignment :=
  model_of_wfHistory_withAxioms hκ hi handler H haxioms

/-- Adapter form for any proposed upstream predicate `P`: it is enough to show that `P` permits
only the canonical standard declarations. -/
theorem model_of_wfHistory_of_axiomPredicate {κ : ℕ → Cardinal.{u}}
    {P : VConstVal → Prop} (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible)
    (handler : StandardAxiom.Handler κ)
    (toStandard : ∀ ci, P ci → IsStandardAxiom ci)
    {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env)
    (haxioms : AxiomsSatisfy P ds) :
    ∃ assignment, ModelSetup κ env assignment :=
  model_of_wfHistory_standard hκ hi handler H (haxioms.mono toStandard)

/-- Build a semantic assignment along a well-formed declaration history containing only
standard axioms. -/
theorem model_of_wfHistory {κ : ℕ → Cardinal.{u}} (hκ : StrictMono κ)
    (hi : ∀ n, (κ n).IsInaccessible)
    (handler : StandardAxiom.Handler κ) {ds : List VDecl} {env : VEnv}
    (H : VEnv.WF' ds env) (haxioms : AxiomsSatisfy IsStandardAxiom ds) :
    ∃ assignment, ModelSetup κ env assignment :=
  model_of_wfHistory_standard hκ hi handler H haxioms

/-- Every well-formed environment whose declaration history contains only standard axioms
has a semantic assignment. -/
theorem model_of_wf {κ : ℕ → Cardinal.{u}} (hκ : StrictMono κ)
    (hi : ∀ n, (κ n).IsInaccessible)
    (handler : StandardAxiom.Handler κ)
    {env : VEnv} (H : env.WF)
    (haxioms : AxiomsSatisfy IsStandardAxiom (Classical.choose H)) :
    ∃ assignment, ModelSetup κ env assignment := by
  let ds := Classical.choose H
  have hds : VEnv.WF' ds env := Classical.choose_spec H
  exact model_of_wfHistory hκ hi handler hds haxioms

end Lean4LeanModel
