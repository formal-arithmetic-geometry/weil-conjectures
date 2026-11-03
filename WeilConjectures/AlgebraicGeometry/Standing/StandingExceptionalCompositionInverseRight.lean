/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standing.StandingExceptionalComposition
public import WeilConjectures.AlgebraicGeometry.Standing.StandingExceptionalCompositionInverse

/-! # Explicit inverse candidate for the standing exceptional compositor

The inverse compact-support compositor is transposed in the reverse direction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] standingExceptionalHomEquiv originCompositionAmbient
  rightDerivedLowerShriek rightDerivedUpperShriek

-- Keep the origin certificates as parameters so the public definitions use their own witnesses.
/- The compiled source definitions carry separate certificates for sheafification and
Grothendieck abelianness. Direct conversion of the resulting derived-category data is
expensive. Build explicit congruence proofs instead; the kernel checks the resulting term.
Adapted from the private transport in WeilConjectures.SmoothPurity.Exceptional.ExceptionalSupportProjectionIso,
with heterogeneous function extensionality for the lambda motives in these definitions. -/
section StandingInstanceTransport
open Lean Meta Elab Tactic

end StandingInstanceTransport

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
-- Allow the congruence tactic to traverse the two compiled instance-certificate expressions.
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

private theorem standingTransposeLeft
    {E₀ E₁ C₀ C₁ : Type*} [Category* E₀] [Category* E₁]
    [Category* C₀] [Category* C₁]
    (A : E₀ ⥤ C₀) (B : E₁ ⥤ C₁) (U : C₁ ⥤ E₁)
    (F : E₀ ⥤ E₁) (R : E₁ ⥤ E₀) (I : C₀ ⥤ C₁)
    (ad : F ⊣ R) (bd : B ⊣ U)
    {L L' : E₀} {M M' : C₀} {N : C₁}
    (a : A.obj L ≅ M) (a' : A.obj L' ≅ M')
    (v : B.obj (F.obj L) ⟶ I.obj (A.obj L))
    (v' : B.obj (F.obj L') ⟶ I.obj (A.obj L'))
    (s : M ⟶ M') (b : I.obj M' ⟶ N) (t : L ⟶ L')
    (ht : A.map t = a.hom ≫ s ≫ a'.inv)
    (hv : B.map (F.map t) ≫ v' = v ≫ I.map (A.map t)) :
    a.inv ≫ A.map (ad.homEquiv _ _
      (bd.homEquiv _ _ (v ≫ I.map a.hom ≫ I.map s ≫ b))) =
    s ≫ a'.inv ≫ A.map (ad.homEquiv _ _
      (bd.homEquiv _ _ (v' ≫ I.map a'.hom ≫ b))) := by
  have hm : A.map t ≫ a'.hom = a.hom ≫ s := by
    rw [ht]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have heq : v ≫ I.map a.hom ≫ I.map s ≫ b =
      B.map (F.map t) ≫ v' ≫ I.map a'.hom ≫ b := by
    rw [reassoc_of% hv, ← I.map_comp_assoc, ← I.map_comp_assoc, hm, I.map_comp,
      Category.assoc]
  rw [heq, bd.homEquiv_naturality_left, ad.homEquiv_naturality_left, A.map_comp]
  simp only [← Category.assoc]
  congr 1
  rw [ht]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem standingHomValue (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K)
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L)
    (b : (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K ⟶ L) :
    standingExceptionalHomEquiv Λ f hK hL b =
      let K' := Classical.choose hK
      let hK' := (Classical.choose_spec hK).1
      let e := Classical.choice (Classical.choose_spec hK).2
      e.inv ≫ (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
        ((Etale.rightDerivedUpperShriekAdjunction Λ f).homEquiv _ _
          ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ _
            ((fixedCompactSupportComparisonIso Λ
              (HasCompactification.compactification f)).inv.app ⟨K', hK'⟩ ≫
                (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map e.hom ≫ b))) := by
  rfl

private theorem standingHomLeft (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    {K K' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K)
    (hK' : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K')
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L) (s : K ⟶ K')
    (b : (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K' ⟶ L) :
    standingExceptionalHomEquiv Λ f hK hL
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map s ≫ b) =
      s ≫ standingExceptionalHomEquiv Λ f hK' hL b := by
  let A := ModuleCat.{u + 1} Λ
  let M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) :=
    ⟨Classical.choose hK, (Classical.choose_spec hK).1⟩
  let M' : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) :=
    ⟨Classical.choose hK', (Classical.choose_spec hK').1⟩
  let e := Classical.choice (Classical.choose_spec hK).2
  let e' := Classical.choice (Classical.choose_spec hK').2
  obtain ⟨t, ht⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map
    M.obj M'.obj M'.property).surjective (e.hom ≫ s ≫ e'.inv)
  have hv := (fixedCompactSupportComparisonIso Λ
    (HasCompactification.compactification f)).inv.naturality
      (ObjectProperty.homMk t : M ⟶ M')
  rw [standingHomValue, standingHomValue]
  exact standingTransposeLeft _ _ _ _ _ _
    (Etale.rightDerivedUpperShriekAdjunction Λ f)
    (derivedComparisonAdjunction A Y) e e' _ _ s b t ht hv

private theorem transposeInverseRight
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    {R V : C} {B : D} {L : E}
    (efR : (F.obj R ⟶ B) ≃ (R ⟶ V))
    (egR : (G.obj (F.obj R) ⟶ L) ≃ (F.obj R ⟶ B))
    (ehR : (H.obj R ⟶ L) ≃ (R ⟶ R))
    (efV : (F.obj V ⟶ B) ≃ (V ⟶ V))
    (egV : (G.obj (F.obj V) ⟶ L) ≃ (F.obj V ⟶ B))
    (ehV : (H.obj V ⟶ L) ≃ (V ⟶ R))
    (nf : ∀ (t : V ⟶ R) (a : F.obj R ⟶ B), efV (F.map t ≫ a) = t ≫ efR a)
    (ng : ∀ (t : V ⟶ R) (a : G.obj (F.obj R) ⟶ L),
      egV (G.map (F.map t) ≫ a) = F.map t ≫ egR a)
    (nh : ∀ (t : V ⟶ R) (a : H.obj R ⟶ L), ehV (H.map t ≫ a) = t ≫ ehR a)
    (alphaR : G.obj (F.obj R) ≅ H.obj R)
    (alphaV : G.obj (F.obj V) ≅ H.obj V)
    (na : ∀ t : V ⟶ R, G.map (F.map t) ≫ alphaR.hom = alphaV.hom ≫ H.map t) :
    ehV (alphaV.inv ≫ egV.symm (efV.symm (𝟙 V))) ≫
      (egR.trans efR) (alphaR.hom ≫ ehR.symm (𝟙 R)) = 𝟙 V := by
  let ER : (R ⟶ R) ≃ (R ⟶ V) :=
    ehR.symm.trans (alphaR.symm.homFromEquiv.trans (egR.trans efR))
  let EV : (V ⟶ R) ≃ (V ⟶ V) :=
    ehV.symm.trans (alphaV.symm.homFromEquiv.trans (egV.trans efV))
  have natural (t : V ⟶ R) (a : R ⟶ R) : EV (t ≫ a) = t ≫ ER a := by
    have hs : ehV.symm (t ≫ a) = H.map t ≫ ehR.symm a := by
      apply ehV.injective
      rw [Equiv.apply_symm_apply, nh, Equiv.apply_symm_apply]
    change efV (egV (alphaV.hom ≫ ehV.symm (t ≫ a))) = _
    rw [hs, ← Category.assoc, ← na t, Category.assoc, ng, nf]
    rfl
  change EV.symm (𝟙 V) ≫ ER (𝟙 R) = 𝟙 V
  rw [← natural (EV.symm (𝟙 V)) (𝟙 R), Category.comp_id, Equiv.apply_symm_apply]

-- These constructions are used through their interfaces in the categorical specialization.

private theorem standingCompositeInverseRight (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace S]
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} Λ)))
    (hLR hLV : DerivedCategory.TStructure.t.plus L)
    (hGR hGV : DerivedCategory.TStructure.t.plus ((rightDerivedUpperShriek Λ g).obj L))
    (hR : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X
      ((rightDerivedUpperShriek Λ (f ≫ g)).obj L))
    (hV : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X
      ((rightDerivedUpperShriek Λ f).obj ((rightDerivedUpperShriek Λ g).obj L)))
    (hFR : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Y
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj
        ((rightDerivedUpperShriek Λ (f ≫ g)).obj L)))
    (hFV : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Y
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj
        ((rightDerivedUpperShriek Λ f).obj ((rightDerivedUpperShriek Λ g).obj L)))) :
    let R := (rightDerivedUpperShriek Λ (f ≫ g)).obj L
    let V := (rightDerivedUpperShriek Λ f).obj ((rightDerivedUpperShriek Λ g).obj L)
    standingExceptionalHomEquiv Λ (f ≫ g) hV hLV
        ((originCompositionAmbient Λ f g).inv.app ⟨V, hV⟩ ≫
          (standingExceptionalHomEquiv Λ g hFV hLV).symm
            ((standingExceptionalHomEquiv Λ f hV hGV).symm (𝟙 V))) ≫
      ((standingExceptionalHomEquiv Λ g hFR hLR).trans
        (standingExceptionalHomEquiv Λ f hR hGR))
        ((originCompositionAmbient Λ f g).hom.app ⟨R, hR⟩ ≫
          (standingExceptionalHomEquiv Λ (f ≫ g) hR hLR).symm (𝟙 R)) = 𝟙 V := by
  exact transposeInverseRight
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (f ≫ g))
    (standingExceptionalHomEquiv Λ f hR hGR)
    (standingExceptionalHomEquiv Λ g hFR hLR)
    (standingExceptionalHomEquiv Λ (f ≫ g) hR hLR)
    (standingExceptionalHomEquiv Λ f hV hGV)
    (standingExceptionalHomEquiv Λ g hFV hLV)
    (standingExceptionalHomEquiv Λ (f ≫ g) hV hLV)
    (fun t a ↦ standingHomLeft Λ f hV hR hGV t a)
    (fun t a ↦ standingHomLeft Λ g hFV hFR hLV
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map t) a)
    (fun t a ↦ standingHomLeft Λ (f ≫ g) hV hR hLV t a)
    ((originCompositionAmbient Λ f g).app ⟨_, hR⟩)
    ((originCompositionAmbient Λ f g).app ⟨_, hV⟩)
    (fun t ↦ by
      have h := (originCompositionAmbient Λ f g).hom.naturality
        (ObjectProperty.homMk t :
          ⟨(rightDerivedUpperShriek Λ f).obj ((rightDerivedUpperShriek Λ g).obj L), hV⟩ ⟶
            ⟨(rightDerivedUpperShriek Λ (f ≫ g)).obj L, hR⟩)
      simpa only [Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.homMk_hom,
        Iso.app_hom] using h)

private meta def standingInstanceCongr
    (cache : IO.Ref (Std.HashMap (Expr × Expr) Expr)) : Nat → Expr → Expr → MetaM Expr
  | 0, _, _ => throwError "instance congruence depth exhausted"
  | fuel + 1, a, b => do
    let a := (← instantiateMVars a).headBeta.consumeMData
    let b := (← instantiateMVars b).headBeta.consumeMData
    let entries ← cache.get
    if let some h := entries[(a, b)]? then return h
    let h ← do
      if a == b then return ← mkHEqRefl a
      if ← isProp (← inferType a) then
        return ← mkAppM ``proof_irrel_heq #[a, b]
      if let .letE _ _ val body _ := a then
        return ← standingInstanceCongr cache fuel (body.instantiate1 val) b
      if let .letE _ _ val body _ := b then
        return ← standingInstanceCongr cache fuel a (body.instantiate1 val)
      if a.isFVar then
        if let some val := ((← getLCtx).get! a.fvarId!).value? then
          return ← standingInstanceCongr cache fuel val b
      if b.isFVar then
        if let some val := ((← getLCtx).get! b.fvarId!).value? then
          return ← standingInstanceCongr cache fuel a val
      if let .lam _ ad ab _ := a then
        if let .lam _ bd bb _ := b then
          let hd ← standingInstanceCongr cache fuel ad bd
          let ed ← mkAppM ``eq_of_heq #[hd]
          return ← withLocalDeclD `x ad fun x ↦
            withLocalDeclD `y bd fun y ↦ do
              let hxyType ← mkHEq x y
              withLocalDeclD `hxy hxyType fun hxy ↦ do
                let entries ← cache.get
                let child ← IO.mkRef (entries.insert (x, y) hxy)
                let hb ← standingInstanceCongr child fuel
                  (ab.instantiate1 x) (bb.instantiate1 y)
                let hf ← mkLambdaFVars #[x, y, hxy] hb
                mkAppM ``Function.hfunext #[ed, hf]
      let af := a.getAppFn
      let bf := b.getAppFn
      if af.isMData then
        return ← standingInstanceCongr cache fuel (mkAppN af.consumeMData a.getAppArgs) b
      if bf.isMData then
        return ← standingInstanceCongr cache fuel a (mkAppN bf.consumeMData b.getAppArgs)
      let sharedType := af.isConstOf ``DerivedCategory ||
        af.isConstOf ``instCategoryDerivedCategory || af.isConstOf ``Sheaf ||
        af.isConstOf ``CategoryTheory.ObjectProperty.FullSubcategory.category ||
        af.isConstOf ``Functor.category || af.isConstOf ``CategoryTheory.Functor ||
        af.isConstOf ``HasDerivedCategory.ofIsGrothendieckAbelian
      if sharedType then
        if ← withReducible (isDefEq a b) then return ← mkHEqRefl a
      if af.isConstOf ``Functor.obj || bf.isConstOf ``Functor.obj then
        if ← withDefault (isDefEq a b) then return ← mkHEqRefl a
      if af == bf && a.getAppArgs.size == b.getAppArgs.size then
        let aa := a.getAppArgs
        let bb := b.getAppArgs
        let ct ← mkHCongrWithArity af aa.size
        let mut ps := #[]
        for i in [:aa.size] do
          let mut h ← standingInstanceCongr cache fuel aa[i]! bb[i]!
          if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
          ps := ps ++ #[aa[i]!, bb[i]!, h]
        let pf := mkAppN ct.proof ps
        if (← inferType pf).isHEq then return pf
        return ← mkAppM ``heq_of_eq #[pf]
      if af.isConstOf ``CommRing.toRing || bf.isConstOf ``CommRing.toRing then
        unless ← isDefEq a b do throwError "coefficient rings differ"
        return ← mkHEqRefl a
      throwError "unmatched instance data: {a} versus {b}"
    cache.modify (·.insert (a, b) h)
    return h

private meta def standingTransportTerm (stx : Syntax) : TacticM Unit :=
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let pf ← Term.elabTerm stx (some target)
    Term.synthesizeSyntheticMVarsNoPostponing
    let pf ← instantiateMVars pf
    let cache ← IO.mkRef ({} : Std.HashMap (Expr × Expr) Expr)
    let q ← standingInstanceCongr cache 500 target (← inferType pf)
    let e ← mkAppM ``eq_of_heq #[q]
    let proof ← mkAppM ``Eq.mpr #[e, pf]
    (← getMainGoal).assign proof

/-- One inverse equation for the explicit counit-transpose candidate.
Source: thm-pur-composition-coherence, exceptional-composition isomorphism, and
pur9-def-upper-shriek-composition, the specified counit formula.
Proof: on bounded-below etale-origin objects, combine the inverse standing Hom
bijection for gf, precomposition by alpha, and the standing Hom bijections for g
and f into E_K : Hom(K,(gf)!L) ≃ Hom(K,f!g!L). The comparison is E_R(id), and the
candidate inverse is E_V.symm(id). Naturality of E in K follows by lifting maps
between etale representatives through fully faithful comparison pullback, then
using naturality of fixedCompactSupportComparisonIso and both adjunction Hom
bijections. Both R=(gf)!L and V=f!g!L lie in this class. The equation E_V(E_V.symm(id))
=id gives b ≫ c=id; applying injectivity of E_R and naturality gives c ≫ b=id.
This theorem records only the displayed one of these two equations. No smoothness,
nonempty-scheme or nonzero-ring hypothesis is used.
(blueprint: lem-route-standing-exceptional-composition-hom-inverse). -/
theorem standingExceptionalComposition_hom_inverse (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y S : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ S)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (L : DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} P.Coefficient) S) :
    standingExceptionalCompositionInverse P f g L ≫
      standingExceptionalComposition P f g L = 𝟙 _ := by
  let : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  let : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  let : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of P.field.k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of P.field.k))
  let : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace
    (S ↘ Spec (.of P.field.k))
  dsimp only [standingExceptionalCompositionInverse, standingExceptionalComposition]
  run_tac do
    let pn := Lean.mkIdent `P
    let fn := Lean.mkIdent `f
    let gn := Lean.mkIdent `g
    let ln := Lean.mkIdent `L
    let stx ← `(standingCompositeInverseRight ($pn).Coefficient $fn $gn ($ln).obj
      _ _ _ _ _ _ _ _)
    standingTransportTerm stx

end AlgebraicGeometry.ProEtale
