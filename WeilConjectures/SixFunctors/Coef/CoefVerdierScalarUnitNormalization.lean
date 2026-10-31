/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorCoherence
import WeilConjectures.SixFunctors.Coef.CoefVerdierScalarUnitModel
import all WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierUnit
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
/-! # Agreement of normalized scalar units used in Verdier duality

Source: the identity scalar normalization in thm-coef-rational-verdier and the
canonical restriction of completed-line scalar coherence.
(blueprint: lem-coef-verdier-scalar-unit-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] CategoryTheory.Functor.mapHomologicalComplex
attribute [local irreducible] HasDerivedCategory.standard Padic
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
  WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
  WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 100000] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local instance 3000] WeilConjectures.integralOperationsCommHasDerivedCategory
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
universe u v w
namespace WeilConjectures
attribute [local irreducible] completedScalarChangeData completedAdicChangeData
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  pbcComplexCounit completedScalarCounit

attribute [local instance 100000] PurCompactSupport.coefficientSiteSmall
  PurCompactSupport.coefficientRingSheafify PurCompactSupport.coefficientAbSheafify
  PurCompactSupport.coefficientAbLocallyBijective

attribute [local irreducible] PurCompactSupport.tensorIdentity

private theorem chainFunctor_eq {C : Type*} [Category C]
    [CategoryTheory.Limits.HasZeroMorphisms C]
    {F G : C ⥤ C} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (h : F = G) :
    F.mapHomologicalComplex (.up ℤ) = G.mapHomologicalComplex (.up ℤ) := by
  subst F
  rfl

private theorem transport_app_heq {C D : Type*} [Category C] [Category D]
    {F G H : C ⥤ D} (h : F = G) (e : G ≅ H) (P : C) :
    HEq ((eqToIso h ≪≫ e).hom.app P) (e.hom.app P) := by
  subst F
  exact heq_of_eq (by simp only [eqToIso_refl, Iso.refl_trans])

private theorem transport_component_heq {C D : Type*} [Category C] [Category D]
    [CategoryTheory.Limits.HasZeroMorphisms D]
    {F G H : C ⥤ CochainComplex D ℤ} (h : F = G) (e : G ≅ H) (P : C) (i : ℤ) :
    HEq (((eqToIso h ≪≫ e).hom.app P).f i) ((e.hom.app P).f i) := by
  subst F
  exact heq_of_eq (by simp only [eqToIso_refl, Iso.refl_trans])

private theorem hom_eval_heq {Y : Scheme.{u}}
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    {M M' N : pbcModules Y R} (hM : M = M') (f : M ⟶ N) (g : M' ⟶ N)
    (hf : HEq f g) (U : Y.ProEtᵒᵖ) (x : M.val.obj U) (y : M'.val.obj U)
    (hx : HEq x y) : (f.val.app U) x = (g.val.app U) y := by
  subst M'
  have hfg : f = g := eq_of_heq hf
  have hxy : x = y := eq_of_heq hx
  rw [hfg, hxy]

private theorem eqToHom_section_heq {Y : Scheme.{u}}
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    {N M M' : pbcModules Y R} (hM : M = M') (h : N = M) (h' : N = M')
    (U : Y.ProEtᵒᵖ) (z : N.val.obj U) :
    HEq ((eqToHom h).val.app U z) ((eqToHom h').val.app U z) := by
  subst M'
  rfl

private theorem map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {M M' N : C} (hM : M = M') (f : M ⟶ N) (g : M' ⟶ N)
    (hf : HEq f g) : HEq (F.map f) (F.map g) := by
  subst M'
  cases hf
  rfl

private theorem iso_inv_heq {C : Type*} [Category C] {A A' B B' : C}
    (hA : A = A') (hB : B = B') (e : A ≅ B) (e' : A' ≅ B')
    (h : HEq e.hom e'.hom) : HEq e.inv e'.inv := by
  subst A' B'
  have he : e = e' := Iso.ext (eq_of_heq h)
  cases he
  rfl

private theorem complex_counit_eq {Y : Scheme.{u}}
    (R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (φ : R ⟶ S)
    (P : CochainComplex (pbcModules Y R) ℤ) :
    pbcComplexCounit φ P =
      (pbcExtensionCounit φ).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  unfold pbcComplexCounit
  have h₁ : (DerivedCategory.quotientCompQhIso (pbcModules Y R)).inv.app P = 𝟙 _ := rfl
  have h₂ : (Functor.mapHomotopyCategoryFactors (pbcExtend φ) (.up ℤ)).hom.app P =
      𝟙 _ := rfl
  have h₃ : (DerivedCategory.quotientCompQhIso (pbcModules Y S)).hom.app
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  rw [h₁, h₂, h₃]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, Category.comp_id]

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u})

attribute [local instance 300000] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory

private theorem scalar_data_eq :
    completedScalarChangeData l E E (AlgHom.id (Padic l) E) X =
      completedAdicChangeData X
        (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X) :=
  Subsingleton.elim _ _

private theorem ordinary_scalar_eq :
    completedOrdinaryScalarExtension l E E (AlgHom.id (Padic l) E) X =
      pbcExtend (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X) := by
  unfold completedOrdinaryScalarExtension pbcExtend reductionChange completedAdicChange
  rw [scalar_data_eq l E X]

private theorem derived_scalar_eq :
    completedDerivedScalarExtension l E E (AlgHom.id (Padic l) E) X =
      pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X) := by
  unfold completedDerivedScalarExtension pbcDerivedExtend reductionDerivedChange
    completedAdicDerivedChange
  rw [scalar_data_eq l E X]

private theorem tensor_section_heq (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U)
    (x : M.val.obj U) :
    HEq (completedScalarTensorSection l E E (AlgHom.id (Padic l) E) X M U s x)
      (pbcTensorSection (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X)
        M U s x) := by
  unfold completedScalarTensorSection pbcTensorSection completedAdicChangeTensor
  exact eqToHom_section_heq (completedIntegralCommRingSheafUnrestricted l E X)
    (congrArg (fun F ↦ F.obj M) (ordinary_scalar_eq l E X)) _ _ U _

private theorem scalar_counit (P : CochainComplex (integralTowerModules l E X) ℤ) :
    HEq (pbcComplexCounit (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X) P)
      (completedScalarCounit l E E (AlgHom.id (Padic l) E) X P) := by
  rw [complex_counit_eq]
  unfold completedScalarCounit pbcExtensionCounit reductionDerivedCounit
  rfl

private theorem verdier_unit_factor (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) :
    (IntegralFiniteExtension.unit l E X K hK).hom =
      (IntegralFiniteExtension.completion l E E (AlgHom.id (Padic l) E) X K hK).inv ≫
        ((eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
      (PurCompactSupport.completedMap_identity l E X)) ≪≫
      PurCompactSupport.tensorIdentity
        (completedIntegralCommRingSheafUnrestricted l E X))).hom.app K := by
  exact RationalVerdier.unit_factor l X E K hK

private theorem complex_unit_eq
    (e : pbcExtend (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X) ≅ 𝟭 _)
    (he : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U)
      (x : M.val.obj U),
      (e.hom.app M).val.app U
        (pbcTensorSection (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X)
          M U s x) = @SMul.smul _ _ (M.val.obj U).isModule.toSMul s x) :
    (eqToIso (chainFunctor_eq (ordinary_scalar_eq l E X)) ≪≫
      (NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ))) =
      completedScalarIdentityMultiplication l E X := by
  apply (completedScalarIdentityMultiplication_existsUnique l E X).unique
  · intro P i U s x
    have hM := congrArg (fun F ↦ F.obj (P.X i)) (ordinary_scalar_eq l E X)
    have hcomp : HEq
        (((eqToIso (chainFunctor_eq (ordinary_scalar_eq l E X)) ≪≫
          (NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ))).hom.app P).f i)
        (e.hom.app (P.X i)) := by
      exact (transport_component_heq (chainFunctor_eq (ordinary_scalar_eq l E X))
        ((NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ))) P i).trans
        (heq_of_eq (by
          simp only [Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
            NatIso.mapHomologicalComplex_hom_app_f,
            Functor.mapHomologicalComplexIdIso_hom_app_f]
          exact Category.comp_id _))
    have hs := hom_eval_heq (completedIntegralCommRingSheafUnrestricted l E X) hM
      (((eqToIso (chainFunctor_eq (ordinary_scalar_eq l E X)) ≪≫
        (NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ))).hom.app P).f i) (e.hom.app (P.X i))
      hcomp U _ _ (tensor_section_heq l E X (P.X i) U s x)
    exact hs.trans (he (P.X i) U s x)
  · exact (completedScalarIdentityMultiplication_existsUnique l E X).exists.choose_spec

private theorem iso_app_hom_heq
    {C C' D D' : Type u} [cC : Category.{v} C] [cC' : Category.{v} C']
    [cD : Category.{v} D] [cD' : Category.{v} D']
    (hC : C = C') (hD : D = D') (hc : HEq cC cC') (hd : HEq cD cD')
    {F G : C ⥤ D} {F' G' : C' ⥤ D'} (hF : HEq F F') (hG : HEq G G')
    (e : F ≅ G) (e' : F' ≅ G') (he : HEq e e')
    (P : C) (P' : C') (hp : HEq P P') : HEq (e.hom.app P) (e'.hom.app P') := by
  subst C' D'
  have hc' : cC = cC' := eq_of_heq hc
  have hd' : cD = cD' := eq_of_heq hd
  subst cC' cD'
  have hF' : F = F' := eq_of_heq hF
  have hG' : G = G' := eq_of_heq hG
  subst F' G'
  have he' : e = e' := eq_of_heq he
  have hp' : P = P' := eq_of_heq hp
  subst e' P'
  rfl

private theorem heq_join {α β γ δ : Sort u} {a : α} {b : β} {c : γ} {d : δ}
    (hab : HEq a b) (hcd : HEq c d) (hbc : HEq b c) : HEq a d :=
  hab.trans (hbc.trans hcd)

private theorem ordinary_unit_model
    (e : pbcExtend (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X) ≅ 𝟭 _)
    (he : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U)
      (x : M.val.obj U),
      (e.hom.app M).val.app U
        (pbcTensorSection (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X)
          M U s x) = @SMul.smul _ _ (M.val.obj U).isModule.toSMul s x)
    (hmodel : ∀ (P : CochainComplex (integralTowerModules l E X) ℤ)
      (_ : proEtaleFlatRepresentatives.{u} X
        (completedIntegralCommRingSheafUnrestricted l E X) P),
      ((eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
      (PurCompactSupport.completedMap_identity l E X)) ≪≫
      PurCompactSupport.tensorIdentity
        (completedIntegralCommRingSheafUnrestricted l E X))).hom.app
          (DerivedCategory.Q.obj P) =
        pbcComplexCounit (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X) P ≫
          DerivedCategory.Q.map (((NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ))).hom.app P)) :
    ∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
      ((eqToIso (derived_scalar_eq l E X) ≪≫
      (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
        (PurCompactSupport.completedMap_identity l E X)) ≪≫
        PurCompactSupport.tensorIdentity
          (completedIntegralCommRingSheafUnrestricted l E X)))).hom.app
            (DerivedCategory.Q.obj P.obj) =
        completedScalarCounit l E E (AlgHom.id (Padic l) E) X P.obj ≫
          DerivedCategory.Q.map ((completedScalarIdentityMultiplication l E X).hom.app P.obj) := by
  intro P
  have hp : proEtaleFlatRepresentatives.{u} X
      (completedIntegralCommRingSheafUnrestricted l E X) P.obj :=
    ⟨P.property.1, P.property.2⟩
  have derived_transport :=
    transport_app_heq (derived_scalar_eq l E X)
      (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
        (PurCompactSupport.completedMap_identity l E X)) ≪≫
        PurCompactSupport.tensorIdentity (completedIntegralCommRingSheafUnrestricted l E X))
      (DerivedCategory.Q.obj P.obj)
  have chain_transport :=
    transport_app_heq (chainFunctor_eq (ordinary_scalar_eq l E X))
      (NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso _ (.up ℤ)) P.obj
  have localized_transport :=
    map_heq DerivedCategory.Q
      (congrArg (fun F ↦ F.obj P.obj) (chainFunctor_eq (ordinary_scalar_eq l E X))) _ _
      chain_transport
  have composite_transport :=
    heq_comp
      (congrArg (fun F ↦ F.obj (DerivedCategory.Q.obj P.obj)) (derived_scalar_eq l E X)).symm
      (congrArg DerivedCategory.Q.obj
        (congrArg (fun F ↦ F.obj P.obj) (chainFunctor_eq (ordinary_scalar_eq l E X))).symm) rfl
      (scalar_counit l E X P.obj) localized_transport.symm
  have h := eq_of_heq ((heq_join derived_transport
    (heq_of_eq (hmodel P.obj hp)) (by
      apply iso_app_hom_heq rfl rfl
      all_goals rfl)).trans composite_transport)
  exact h.trans (congrArg (fun z ↦
    completedScalarCounit l E E (AlgHom.id (Padic l) E) X P.obj ≫
      DerivedCategory.Q.map (z.hom.app P.obj)) (complex_unit_eq l E X e he))

private theorem ordinary_unit_eq
    (e : pbcExtend (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X) ≅ 𝟭 _)
    (he : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U)
      (x : M.val.obj U),
      (e.hom.app M).val.app U
        (pbcTensorSection (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X)
          M U s x) = @SMul.smul _ _ (M.val.obj U).isModule.toSMul s x)
    (hmodel : ∀ (P : CochainComplex (integralTowerModules l E X) ℤ)
      (_ : proEtaleFlatRepresentatives.{u} X
        (completedIntegralCommRingSheafUnrestricted l E X) P),
      ((eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
      (PurCompactSupport.completedMap_identity l E X)) ≪≫
      PurCompactSupport.tensorIdentity
        (completedIntegralCommRingSheafUnrestricted l E X))).hom.app
          (DerivedCategory.Q.obj P) =
        pbcComplexCounit (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X) P ≫
          DerivedCategory.Q.map (((NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ))).hom.app P)) :
    (eqToIso (derived_scalar_eq l E X) ≪≫
      (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
        (PurCompactSupport.completedMap_identity l E X)) ≪≫
        PurCompactSupport.tensorIdentity
          (completedIntegralCommRingSheafUnrestricted l E X))) =
        CompletedLineTensor.ordinaryUnit l E X := by
  exact (CompletedLineTensor.ordinaryUnit_existsUnique l E X).unique
    (ordinary_unit_model l E X e he hmodel)
    (CompletedLineTensor.ordinaryUnit_existsUnique l E X).exists.choose_spec

private theorem unit_formula_transfer
    {C C' D D' : Type u} [cC : Category.{v} C] [cC' : Category.{v} C']
    [cD : Category.{w} D] [cD' : Category.{w} D']
    {Q : C ⥤ D} {Q' : C' ⥤ D'} {F : C ⥤ C} {F' : C' ⥤ C'}
    {G : D ⥤ D} {G' : D' ⥤ D'}
    {e : F ≅ 𝟭 C} {e' : F' ≅ 𝟭 C'} {g : G ≅ 𝟭 D} {g' : G' ≅ 𝟭 D'}
    {P : C} {P' : C'}
    {ε : G.obj (Q.obj P) ⟶ Q.obj (F.obj P)}
    {ε' : G'.obj (Q'.obj P') ⟶ Q'.obj (F'.obj P')}
    (h : g.hom.app (Q.obj P) = ε ≫ Q.map (e.hom.app P))
    (hC : C = C') (hD : D = D') (hc : HEq cC cC') (hd : HEq cD cD')
    (hQ : HEq Q Q') (hF : HEq F F') (hG : HEq G G')
    (he : HEq e e') (hg : HEq g g') (hP : HEq P P') (hε : HEq ε ε') :
    g'.hom.app (Q'.obj P') = ε' ≫ Q'.map (e'.hom.app P') := by
  subst C' D'
  have hc' : cC = cC' := eq_of_heq hc
  have hd' : cD = cD' := eq_of_heq hd
  subst cC' cD'
  have hQ' : Q = Q' := eq_of_heq hQ
  have hF' : F = F' := eq_of_heq hF
  have hG' : G = G' := eq_of_heq hG
  subst Q' F' G'
  have he' : e = e' := eq_of_heq he
  have hg' : g = g' := eq_of_heq hg
  have hP' : P = P' := eq_of_heq hP
  subst e' g' P'
  have hε' : ε = ε' := eq_of_heq hε
  subst ε'
  exact h

private theorem constructed_ordinary_unit_eq :
    (eqToIso (derived_scalar_eq l E X) ≪≫
      (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
        (PurCompactSupport.completedMap_identity l E X)) ≪≫
        PurCompactSupport.tensorIdentity
          (completedIntegralCommRingSheafUnrestricted l E X))) =
        CompletedLineTensor.ordinaryUnit l E X := by
  let e := identityScalarUnit
    (completedIntegralCommRingSheafUnrestricted l E X)
    (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X)
    (completedCoefficientMap_id l E X)
  have he (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U)
      (x : M.val.obj U) := (scalar_identity_unit_model
    (completedIntegralCommRingSheafUnrestricted l E X)
    (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X)
    (completedCoefficientMap_id l E X)).1 M U s x
  have hd := (scalar_identity_unit_model
    (completedIntegralCommRingSheafUnrestricted l E X)
    (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X)
    (completedCoefficientMap_id l E X)).2
  have hd' (P : CochainComplex (integralTowerModules l E X) ℤ)
      (hp : proEtaleFlatRepresentatives.{u} X
        (completedIntegralCommRingSheafUnrestricted l E X) P) :
      ((eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
      (PurCompactSupport.completedMap_identity l E X)) ≪≫
      PurCompactSupport.tensorIdentity
        (completedIntegralCommRingSheafUnrestricted l E X))).hom.app
          (DerivedCategory.Q.obj P) =
        pbcComplexCounit (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X) P ≫
          DerivedCategory.Q.map (((NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ))).hom.app P) := by
    apply unit_formula_transfer (hd P hp) rfl rfl
    all_goals rfl
  exact ordinary_unit_eq l E X e he hd'

private theorem derived_unit_component_heq
    (K : IntegralVerdier.Ambient l E X) : HEq (((eqToIso (derived_scalar_eq l E X) ≪≫
      (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
        (PurCompactSupport.completedMap_identity l E X)) ≪≫
        PurCompactSupport.tensorIdentity
          (completedIntegralCommRingSheafUnrestricted l E X)))).hom.app K)
      (((eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
      (PurCompactSupport.completedMap_identity l E X)) ≪≫
      PurCompactSupport.tensorIdentity
        (completedIntegralCommRingSheafUnrestricted l E X))).hom.app K) := by
  refine heq_join
    (transport_app_heq (derived_scalar_eq l E X)
      (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
        (PurCompactSupport.completedMap_identity l E X)) ≪≫
        PurCompactSupport.tensorIdentity
          (completedIntegralCommRingSheafUnrestricted l E X)) K)
    (HEq.rfl) ?_
  apply iso_app_hom_heq rfl rfl
  all_goals rfl

/-- The normalized intrinsic integral unit is the completed Verdier scalar unit.
Source: thm-coef-rational-verdier, identity-extension paragraph; Stacks 03DA and 06YY.
(blueprint: lem-coef-verdier-scalar-unit-normalization).

Proof: use the tensor and K-flat model for the identity scalar unit. Multiplication
uniqueness identifies its chain unit with completed coefficient multiplication.
The good-complex localization then identifies its derived unit with the completed
ordinary unitor. Canonical restriction identifies the intrinsic unit with this
unitor conjugated by completion. Both completion maps are the same specified map;
the explicit functor transports give equal composites. Zero objects and the empty
scheme are included. -/
theorem integral_unit_normalization (K : sfIntegralConstructibleCategory l E X) :
    ((sfIntegralScalarUnit l E X 0 (Fact.out : l.Prime).ne_zero).hom.app K).hom =
      (IntegralFiniteExtension.unit l E X K.obj K.property.1).hom := by
  have hu := constructed_ordinary_unit_eq l E X
  have hc := (CompletedLineTensor.canonical_restriction l E E (AlgHom.id (Padic l) E)
    E (AlgHom.id (Padic l) E) X 0 (Fact.out : l.Prime).ne_zero).2.1 K
  have hD := derived_unit_component_heq l E X K.obj
  have hT := congrArg (fun F ↦ F.obj K.obj) (derived_scalar_eq l E X)
  have hχ : HEq
      ((CompletedLineTensor.chi l E X E (AlgHom.id (Padic l) E) K.obj
        (CompletedLineTensor.intrinsic_complete l E X K)).symm.hom)
      ((IntegralFiniteExtension.completion l E E (AlgHom.id (Padic l) E) X
        K.obj K.property.1).symm.hom) := by
    exact iso_inv_heq hT rfl _ _ (by rfl)
  have hN := (heq_of_eq
    (congrArg (fun z ↦ z.hom.app K.obj) hu.symm)).trans hD
  have ht := heq_comp rfl hT rfl hχ hN
  have hc' := eq_of_heq (hc.trans ht)
  exact hc'.trans (verdier_unit_factor l E X K.obj K.property.1).symm
end WeilConjectures
