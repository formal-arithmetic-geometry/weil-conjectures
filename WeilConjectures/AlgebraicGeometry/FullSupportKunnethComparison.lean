/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantProjectionMap
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedCoefficientOpenTensor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal

/-! # Full-support normalization of the supported Künneth pairing

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/lem-pur-kunneth-supported.proof.md,
paragraphs 1--2.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

-- Choose the canonical ring and braiding instances before constructing derived functors.
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local instance 21000] sheafBraidedCategory
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor upperStar

section Normalization
variable {C : Type v} {D : Type w} [Category.{u + 1} C] [Category.{u + 1} D]
  [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} C] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [SymmetricCategory C] [SymmetricCategory D]
  [MonoidalClosed C] [MonoidalClosed D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  (H G F₁ F₂ : C ⥤ D)
  [H.Additive] [G.Additive] [F₁.Additive] [F₂.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [H.Monoidal] [H.PreservesFlat] [H.IsLeftAdjoint] [G.IsLeftAdjoint]
  (e₀ : H ≅ G) (e₁ : H ≅ F₁) (e₂ : H ≅ F₂)
  (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
    (((Functor.whiskeringLeft₂ D).obj F₁).obj F₂).obj (curriedTensor D))

omit [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂] [H.PreservesFlat] in
private theorem comparison_complex_transport
    (hτ : ∀ M N, e₀.hom.app (M ⊗ N) ≫ (τ.app M).app N =
      Functor.OplaxMonoidal.δ H M N ≫ (e₁.hom.app M ⊗ₘ e₂.hom.app N))
    (P Q : CochainComplex C ℤ) :
    (NatTrans.mapHomologicalComplex e₀.hom (.up ℤ)).app (P ⊗ Q) ≫
        ((supportedComplexComparisonNatTrans G F₁ F₂ τ).app P).app Q =
      ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) H).app P).app Q ≫
        ((NatTrans.mapHomologicalComplex e₁.hom (.up ℤ)).app P ⊗ₘ
          (NatTrans.mapHomologicalComplex e₂.hom (.up ℤ)).app Q) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map H
  intro r s hrs
  have hn := e₀.hom.naturality
    (HomologicalComplex.ιMapBifunctor P Q (curriedTensor C) (.up ℤ) r s n hrs)
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f]
  erw [← Category.assoc, hn, Category.assoc]
  erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX]
  erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simpa only [HomologicalComplex.mapBifunctorComparisonApp,
    Functor.OplaxMonoidal.δNatTrans, curriedTensor,
    NatTrans.mapHomologicalComplex_app_f, MonoidalCategory.tensorHom_def, Category.assoc,
    Functor.mapHomologicalComplex, Functor.comp_obj] using
      congrArg (fun k ↦ k ≫ HomologicalComplex.ιMapBifunctor
        ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
        ((F₂.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ) r s n hrs)
        (hτ (P.X r) (Q.X s))

private theorem comparison_derived_transport_normalized
    (hτ : ∀ M N, e₀.hom.app (M ⊗ N) ≫ (τ.app M).app N =
      Functor.OplaxMonoidal.δ H M N ≫ (e₁.hom.app M ⊗ₘ e₂.hom.app N))
    (P Q : CochainComplex C ℤ) :
    let d₀ := Functor.mapDerivedCategoryNatIso e₀
    let d₁ := Functor.mapDerivedCategoryNatIso e₁
    let d₂ := Functor.mapDerivedCategoryNatIso e₂
    (d₀.inv.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
        (H.mapDerivedCategoryTensorComparison.app (DerivedCategory.Q.obj P)).app
          (DerivedCategory.Q.obj Q) ≫
        (d₁.hom.app (DerivedCategory.Q.obj P) ⊗ₘ
          d₂.hom.app (DerivedCategory.Q.obj Q))) ≫
      (F₁.mapDerivedCategoryFactors.hom.app P ⊗ₘ F₂.mapDerivedCategoryFactors.hom.app Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
        ((F₂.mapHomologicalComplex (.up ℤ)).obj Q) =
    G.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      G.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
      DerivedCategory.Q.map (((supportedComplexComparisonNatTrans G F₁ F₂ τ).app P).app Q) := by
  dsimp only
  apply (cancel_epi ((Functor.mapDerivedCategoryNatIso e₀).hom.app
    (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q))).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← tensorHom_comp_tensorHom_assoc, Functor.LaxMonoidal.μ_natural]
  have hH := tensor_facQ_of_fach H H.mapDerivedCategoryTensorComparison
    (Functor.mapDerivedCategoryTensorComparison_app_app_comp H) P Q
  rw [reassoc_of% hH]
  simp only [← Functor.map_comp]
  rw [← comparison_complex_transport H G F₁ F₂ e₀ e₁ e₂ τ hτ P Q]
  simp only [Functor.map_comp]
  rw [← Functor.mapDerivedCategoryNatIso_fac_assoc]
  simpa only [Category.assoc] using congrArg (fun k ↦
    k ≫ G.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
    DerivedCategory.Q.map (((supportedComplexComparisonNatTrans G F₁ F₂ τ).app P).app Q))
      ((Functor.mapDerivedCategoryNatIso e₀).hom.naturality
        (Functor.LaxMonoidal.μ DerivedCategory.Q P Q))

private noncomputable def transportedComparison :
    (Functor.postcompose₂.obj G.mapDerivedCategory).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
        F₂.mapDerivedCategory).obj (curriedTensor _) :=
  (Functor.postcompose₂.map (Functor.mapDerivedCategoryNatIso e₀).inv).app _ ≫
    H.mapDerivedCategoryTensorComparison ≫
    (((Functor.whiskeringLeft₂ _).map (Functor.mapDerivedCategoryNatIso e₁).hom).app
      H.mapDerivedCategory).app (curriedTensor _) ≫
    (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).map
      (Functor.mapDerivedCategoryNatIso e₂).hom).app (curriedTensor _)

omit [G.IsLeftAdjoint] in
private theorem transportedComparison_app (M N : _root_.DerivedCategory C) :
    ((transportedComparison H G F₁ F₂ e₀ e₁ e₂).app M).app N =
      (Functor.mapDerivedCategoryNatIso e₀).inv.app (M ⊗ N) ≫
        (H.mapDerivedCategoryTensorComparison.app M).app N ≫
        ((Functor.mapDerivedCategoryNatIso e₁).hom.app M ⊗ₘ
          (Functor.mapDerivedCategoryNatIso e₂).hom.app N) := by
  simp only [transportedComparison, NatTrans.comp_app, MonoidalCategory.tensorHom_def]
  rfl

private theorem comparison_derived_transport [F₂.PreservesFlat] [F₂.IsLeftAdjoint]
    (hτ : ∀ M N, e₀.hom.app (M ⊗ N) ≫ (τ.app M).app N =
      Functor.OplaxMonoidal.δ H M N ≫ (e₁.hom.app M ⊗ₘ e₂.hom.app N))
    (t : supportedDerivedComparisonHom G F₁ F₂)
    (ht : supportedDerivedComparisonCondition G F₁ F₂
      (supportedComplexComparisonNatTrans G F₁ F₂ τ) t)
    (M N : _root_.DerivedCategory C) :
    t M N = (Functor.mapDerivedCategoryNatIso e₀).inv.app (M ⊗ N) ≫
      (H.mapDerivedCategoryTensorComparison.app M).app N ≫
      ((Functor.mapDerivedCategoryNatIso e₁).hom.app M ⊗ₘ
        (Functor.mapDerivedCategoryNatIso e₂).hom.app N) := by
  let γ := transportedComparison H G F₁ F₂ e₀ e₁ e₂
  have hγ : supportedDerivedComparisonCondition G F₁ F₂
      (supportedComplexComparisonNatTrans G F₁ F₂ τ) (fun M N ↦ (γ.app M).app N) := by
    constructor
    · intro M M' N N' a b
      have ha := congr_app (γ.naturality a) N
      have hb := (γ.app M').naturality b
      change G.mapDerivedCategory.map (a ▷ N) ≫ (γ.app M').app N =
        (γ.app M).app N ≫ (F₁.mapDerivedCategory.map a ▷ F₂.mapDerivedCategory.obj N) at ha
      change G.mapDerivedCategory.map (M' ◁ b) ≫ (γ.app M').app N' =
        (γ.app M').app N ≫ (F₁.mapDerivedCategory.obj M' ◁ F₂.mapDerivedCategory.map b) at hb
      rw [MonoidalCategory.tensorHom_def, Functor.map_comp, Category.assoc, hb,
        ← Category.assoc, ha, Category.assoc, ← MonoidalCategory.tensorHom_def]
    · intro P Q
      dsimp only
      rw [show eqToHom (supportedComplexTensor_eq
        ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
        ((F₂.mapHomologicalComplex (.up ℤ)).obj Q)) = 𝟙 _ from rfl,
        CategoryTheory.Functor.map_id, Category.comp_id]
      rw [show (γ.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) = _ from
        transportedComparison_app H G F₁ F₂ e₀ e₁ e₂ _ _]
      exact (comparison_derived_transport_normalized H G F₁ F₂ e₀ e₁ e₂ τ hτ P Q).symm
  have he := (derivedComparison_unique G F₁ F₂
    (supportedComplexComparisonNatTrans G F₁ F₂ τ)).unique ht hγ
  exact congrFun (congrFun he M) N |>.trans
    (transportedComparison_app H G F₁ F₂ e₀ e₁ e₂ M N)

private theorem comparison_derived_transport_left [F₂.PreservesFlat] [F₂.IsLeftAdjoint]
    (hτ : ∀ M N, e₀.hom.app (M ⊗ N) ≫ (τ.app M).app N =
      Functor.OplaxMonoidal.δ H M N ≫ (e₁.hom.app M ⊗ₘ e₂.hom.app N))
    (t : supportedDerivedComparisonHom G F₁ F₂)
    (ht : supportedDerivedComparisonCondition G F₁ F₂
      (supportedComplexComparisonNatTrans G F₁ F₂ τ) t)
    (M N : _root_.DerivedCategory C) :
    (Functor.mapDerivedCategoryNatIso e₀).hom.app (M ⊗ N) ≫ t M N =
      (H.mapDerivedCategoryTensorComparison.app M).app N ≫
        ((Functor.mapDerivedCategoryNatIso e₁).hom.app M ⊗ₘ
          (Functor.mapDerivedCategoryNatIso e₂).hom.app N) := by
  rw [comparison_derived_transport H G F₁ F₂ e₀ e₁ e₂ τ hτ t ht M N]
  simp only [Iso.hom_inv_id_app_assoc]

end Normalization

section SchemeNormalization
variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C] (T : Scheme.{u})
  (H G F₁ F₂ : C ⥤ Sheaf T.smallEtaleTopology C)
  [H.Additive] [G.Additive] [F₁.Additive] [F₂.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [H.Monoidal] [H.PreservesFlat] [H.IsLeftAdjoint] [G.IsLeftAdjoint]
  [F₂.PreservesFlat] [F₂.IsLeftAdjoint]

private theorem comparison_scheme_transport
    (e₀ : H ≅ G) (e₁ : H ≅ F₁) (e₂ : H ≅ F₂)
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj (supportedSheafTensorGeneric C T))
    (hτ : ∀ M N, e₀.hom.app (M ⊗ N) ≫ (τ.app M).app N =
      Functor.OplaxMonoidal.δ H M N ≫ (e₁.hom.app M ⊗ₘ e₂.hom.app N))
    (t : supportedSchemeDerivedHom C T G F₁ F₂)
    (ht : supportedSchemeDerivedCondition C T G F₁ F₂ τ t)
    (M N : _root_.DerivedCategory C) :
    (Functor.mapDerivedCategoryNatIso e₀).hom.app (M ⊗ N) ≫
      supportedSchemeDerivedApply C T G F₁ F₂ t M N =
    (H.mapDerivedCategoryTensorComparison.app M).app N ≫
      ((Functor.mapDerivedCategoryNatIso e₁).hom.app M ⊗ₘ
        (Functor.mapDerivedCategoryNatIso e₂).hom.app N) := by
  exact comparison_derived_transport_left H G F₁ F₂ e₀ e₁ e₂ τ hτ t ht M N

end SchemeNormalization

section AdjointTransport
variable {C D : Type*} [Category C] [Category D]
  {F F' : C ⥤ D} {R R' : D ⥤ C}

private noncomputable def comparisonRightIso
    (e : F ≅ F') (a : F ⊣ R) (a' : F' ⊣ R') : R' ≅ R :=
  Adjunction.rightAdjointUniq (a'.ofNatIsoLeft e.symm) a

private theorem comparisonRightIso_counit
    (e : F ≅ F') (a : F ⊣ R) (a' : F' ⊣ R') (K : D) :
    F.map ((comparisonRightIso e a a').hom.app K) ≫ a.counit.app K =
      e.hom.app (R'.obj K) ≫ a'.counit.app K := by
  exact Adjunction.rightAdjointUniq_hom_app_counit (a'.ofNatIsoLeft e.symm) a K

private theorem comparisonRightIso_transpose
    (e : F ≅ F') (a : F ⊣ R) (a' : F' ⊣ R') {M : C} {K : D}
    (t : F'.obj M ⟶ K) :
    a.homEquiv _ _ (e.hom.app M ≫ t) =
      a'.homEquiv _ _ t ≫ (comparisonRightIso e a a').hom.app K := by
  apply (a.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    comparisonRightIso_counit, e.hom.naturality_assoc]
  rw [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]

private theorem comparisonMate_congr
    (e : F ≅ F') (a : F ⊣ R) (a' : F' ⊣ R') {M M' : C} {K : D}
    (s : M ⟶ M') (t : F'.obj M ⟶ K) (t' : F.obj M' ⟶ K)
    (h : e.hom.app M ≫ t = F.map s ≫ t') :
    a'.homEquiv _ _ t ≫ (comparisonRightIso e a a').hom.app K =
      s ≫ a.homEquiv _ _ t' := by
  rw [← comparisonRightIso_transpose, h, Adjunction.homEquiv_naturality_left]

end AdjointTransport

attribute [local instance] supportedHasSheafify supportedHasWeakSheafify
attribute [local instance 2000] CommRing.toRing monoidalConstantSheaf

private noncomputable def fullCoefficientIso
    (A : Type (u + 1)) [CommRing A] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIso i] :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ≅ supportedCoefficients A i := by
  have (M : ModuleCat.{u + 1} A) : IsIso (supportedCoefficientQuotient A i M) := by
    unfold supportedCoefficientQuotient
    rw [Adjunction.homEquiv_unit]
    have : (upperStar (ModuleCat.{u + 1} A) i).IsEquivalence :=
      isEquivalence_upperStar_of_isIso (ModuleCat.{u + 1} A) i
    have hu : IsIso (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit :=
      Adjunction.unit_isIso_of_L_fully_faithful _
    exact ((asIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app _)) ≪≫
      (lowerStar (ModuleCat.{u + 1} A) i).mapIso
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app M)).isIso_hom
  letI (M : ModuleCat.{u + 1} A) : IsIso ((coefficientQuotientNat A i).app M) := this M
  have : IsIso (coefficientQuotientNat A i) := NatIso.isIso_of_isIso_app _
  exact asIso (coefficientQuotientNat A i)

private noncomputable def fullPulledCoefficientIso
    (A : Type (u + 1)) [CommRing A] {X T : Scheme.{u}} (p : T ⟶ X) :
    constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ≅
      supportedCoefficients A (𝟙 X) ⋙ upperStar (ModuleCat.{u + 1} A) p :=
  (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) p).symm ≪≫
    Functor.isoWhiskerRight (fullCoefficientIso A (𝟙 X))
      (upperStar (ModuleCat.{u + 1} A) p)

private noncomputable def fullFirstCoefficientIso
    (A : Type (u + 1)) [CommRing A] {B X Y : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) :
    constantSheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A) ≅
      supportedFirstCoefficients A f g (𝟙 X) :=
  fullPulledCoefficientIso A (pullback.fst f g)

private noncomputable def fullSecondCoefficientIso
    (A : Type (u + 1)) [CommRing A] {B X Y : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) :
    constantSheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A) ≅
      supportedSecondCoefficients A f g (𝟙 Y) :=
  fullPulledCoefficientIso A (pullback.snd f g)

private instance fullProduct_isIso {B X Y : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) :
    IsIso (supportedProductImmersion f g (𝟙 X) (𝟙 Y)) := by
  unfold supportedProductImmersion
  infer_instance

private theorem fullCoefficientTensor_sheaf_normalized
    (A : Type (u + 1)) [CommRing A] {B X Y : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (M N : ModuleCat.{u + 1} A) :
      (fullCoefficientIso A (supportedProductImmersion f g (𝟙 X) (𝟙 Y))).hom.app (M ⊗ N) ≫
        ((supportedCoefficientTensorNatTrans A f g (𝟙 X) (𝟙 Y)).app M).app N =
      Functor.OplaxMonoidal.δ
        (constantSheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A)) M N ≫
        ((fullFirstCoefficientIso A f g).hom.app M ⊗ₘ
          (fullSecondCoefficientIso A f g).hom.app N) := by
  change supportedCoefficientQuotient A _ (M ⊗ N) ≫
    supportedCoefficientTensor A f g (𝟙 X) (𝟙 Y) M N =
      supportedConstantTensor A (pullback f g) M N ≫
        ((firstCoefficientQuotientNat A f g (𝟙 X)).app M ⊗ₘ
          (secondCoefficientQuotientNat A f g (𝟙 Y)).app N)
  exact coefficientTensor_spec A f g (𝟙 X) (𝟙 Y) M N

private theorem fullCoefficientTensor_normalized
    (A : Type (u + 1)) [CommRing A] {B X Y : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (M N : _root_.DerivedCategory (ModuleCat.{u + 1} A)) :
    (Functor.mapDerivedCategoryNatIso
        (fullCoefficientIso A (supportedProductImmersion f g (𝟙 X) (𝟙 Y)))).hom.app (M ⊗ N) ≫
      supportedCoefficientTensorDerived A f g (𝟙 X) (𝟙 Y) M N =
    ((constantSheaf (pullback f g).smallEtaleTopology
        (ModuleCat.{u + 1} A)).mapDerivedCategoryTensorComparison.app M).app N ≫
      ((Functor.mapDerivedCategoryNatIso (fullFirstCoefficientIso A f g)).hom.app M ⊗ₘ
        (Functor.mapDerivedCategoryNatIso (fullSecondCoefficientIso A f g)).hom.app N) := by
  have : (supportedSecondCoefficients A f g (𝟙 Y)).PreservesFlat :=
    secondCoefficient_flat A f g (𝟙 Y)
  have : (supportedSecondCoefficients A f g (𝟙 Y)).IsLeftAdjoint :=
    secondCoefficient_leftAdjoint A f g (𝟙 Y)
  exact comparison_scheme_transport (ModuleCat.{u + 1} A) (pullback f g)
    (constantSheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A))
    (supportedCoefficients A (supportedProductImmersion f g (𝟙 X) (𝟙 Y)))
    (supportedFirstCoefficients A f g (𝟙 X)) (supportedSecondCoefficients A f g (𝟙 Y))
    (fullCoefficientIso A (supportedProductImmersion f g (𝟙 X) (𝟙 Y)))
    (fullFirstCoefficientIso A f g) (fullSecondCoefficientIso A f g)
    (supportedCoefficientTensorNatTrans A f g (𝟙 X) (𝟙 Y))
    (fullCoefficientTensor_sheaf_normalized A f g)
    (exists_unique_supportedCoefficientTensorDerived A f g (𝟙 X) (𝟙 Y)).choose
    (exists_unique_supportedCoefficientTensorDerived A f g (𝟙 X) (𝟙 Y)).choose_spec.1 M N

private noncomputable def fullDerivedCoefficientIso
    (A : Type (u + 1)) [CommRing A] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIso i] :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).leftDerivedFunctor ≅
      (supportedCoefficients A i).mapDerivedCategory :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).leftDerivedFunctorIsoMapDerivedCategory
    ≪≫ Functor.mapDerivedCategoryNatIso (fullCoefficientIso A i)

private noncomputable def fullSectionsIso
    (A : Type (u + 1)) [CommRing A] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIso i] :
    supportedSectionsDerived A i ≅ rightDerivedGlobalSections (ModuleCat.{u + 1} A) X :=
  comparisonRightIso (fullDerivedCoefficientIso A i)
    (derivedConstantGlobalSectionsAdjunction (ModuleCat.{u + 1} A) X)
    (supportedCoefficientDerivedAdjunction A i)

private theorem fullCoefficientTensor_left_normalized
    (A : Type (u + 1)) [CommRing A] {B X Y : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (M N : _root_.DerivedCategory (ModuleCat.{u + 1} A)) :
    (fullDerivedCoefficientIso A
        (supportedProductImmersion f g (𝟙 X) (𝟙 Y))).hom.app (M ⊗ N) ≫
      supportedCoefficientTensorDerived A f g (𝟙 X) (𝟙 Y) M N =
    ((constantSheaf (pullback f g).smallEtaleTopology
        (ModuleCat.{u + 1} A)).leftDerivedTensorComparison.app M).app N ≫
      (((constantSheaf (pullback f g).smallEtaleTopology
          (ModuleCat.{u + 1} A)).leftDerivedFunctorIsoMapDerivedCategory.hom.app M ≫
        (Functor.mapDerivedCategoryNatIso (fullFirstCoefficientIso A f g)).hom.app M) ⊗ₘ
       ((constantSheaf (pullback f g).smallEtaleTopology
          (ModuleCat.{u + 1} A)).leftDerivedFunctorIsoMapDerivedCategory.hom.app N ≫
        (Functor.mapDerivedCategoryNatIso (fullSecondCoefficientIso A f g)).hom.app N)) := by
  simp only [fullDerivedCoefficientIso, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    fullCoefficientTensor_normalized, Functor.mapDerivedCategoryTensorComparison_app_app,
    Iso.hom_inv_id_app_assoc, tensorHom_comp_tensorHom, Category.assoc]

private theorem fullPulledEvaluation
    (A : Type (u + 1)) [CommRing A] {X T : Scheme.{u}} (p : T ⟶ X)
    (M : _root_.DerivedCategory (ModuleCat.{u + 1} A))
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (t : (supportedCoefficients A (𝟙 X)).mapDerivedCategory.obj M ⟶ K) :
    ((constantSheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} A)).leftDerivedFunctorIsoMapDerivedCategory).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) p).symm ≪≫
          Functor.isoWhiskerRight (fullCoefficientIso A (𝟙 X))
            (upperStar (ModuleCat.{u + 1} A) p))).hom.app M ≫
      (Functor.mapDerivedCategoryCompIso (supportedCoefficients A (𝟙 X))
        (upperStar (ModuleCat.{u + 1} A) p)).hom.app M ≫
      (upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.map t ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).inv.app K =
    (derivedConstantPullbackIso (ModuleCat.{u + 1} A) p).hom.app M ≫
      (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.map
        ((fullDerivedCoefficientIso A (𝟙 X)).hom.app M ≫ t) := by
  let C := ModuleCat.{u + 1} A
  have hw := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight
    (fullCoefficientIso A (𝟙 X)) (upperStar C p)) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hw
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% hw]
  simp only [derivedConstantPullbackIso, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, fullDerivedCoefficientIso,
    leftDerivedUpperStarIsoMapDerivedCategory,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [← (upperStar C p).leftDerivedFunctorIsoMapDerivedCategory.inv.naturality]
  dsimp only [C] at *
  erw [← CategoryTheory.Functor.map_comp_assoc]
  erw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]

private theorem fullPullbackEvaluation_normalized
    (A : Type (u + 1)) [CommRing A] {X T : Scheme.{u}} (p : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ((constantSheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} A)).leftDerivedFunctorIsoMapDerivedCategory).hom.app
        ((supportedSectionsDerived A (𝟙 X)).obj K) ≫
      (Functor.mapDerivedCategoryNatIso (fullPulledCoefficientIso A p)).hom.app
        ((supportedSectionsDerived A (𝟙 X)).obj K) ≫
      (Functor.mapDerivedCategoryCompIso (supportedCoefficients A (𝟙 X))
        (upperStar (ModuleCat.{u + 1} A) p)).hom.app _ ≫
      (upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.map
        ((supportedCoefficientDerivedAdjunction A (𝟙 X)).counit.app K) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).inv.app K =
    (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).leftDerivedFunctor.map
        ((fullSectionsIso A (𝟙 X)).hom.app K) ≫
      ordinaryKunnethPulledCounit (ModuleCat.{u + 1} A) p K := by
  unfold fullPulledCoefficientIso
  erw [fullPulledEvaluation A p ((supportedSectionsDerived A (𝟙 X)).obj K) K
    ((supportedCoefficientDerivedAdjunction A (𝟙 X)).counit.app K)]
  rw [comparisonRightIso_counit (fullDerivedCoefficientIso A (𝟙 X))
    (derivedConstantGlobalSectionsAdjunction (ModuleCat.{u + 1} A) X)
    (supportedCoefficientDerivedAdjunction A (𝟙 X)) K |>.symm]
  simp only [Functor.map_comp, ordinaryKunnethPulledCounit]
  exact ((derivedConstantPullbackIso (ModuleCat.{u + 1} A) p).hom.naturality_assoc _ _).symm

private theorem fullTensorEvaluation_normalized
    (A : Type (u + 1)) [CommRing A] {B X Y : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (fullDerivedCoefficientIso A
        (supportedProductImmersion f g (𝟙 X) (𝟙 Y))).hom.app _ ≫
      (supportedCoefficientTensorDerived A f g (𝟙 X) (𝟙 Y)
        ((supportedSectionsDerived A (𝟙 X)).obj K)
        ((supportedSectionsDerived A (𝟙 Y)).obj L) ≫
      supportedDerivedTensorMap A (pullback f g)
        (supportedFirstEvaluation A f g (𝟙 X) K)
        (supportedSecondEvaluation A f g (𝟙 Y) L)) =
    (constantSheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A)).leftDerivedFunctor.map
        ((fullSectionsIso A (𝟙 X)).hom.app K ⊗ₘ (fullSectionsIso A (𝟙 Y)).hom.app L) ≫
      (((constantSheaf (pullback f g).smallEtaleTopology
          (ModuleCat.{u + 1} A)).leftDerivedTensorComparison.app _).app _ ≫
        (ordinaryKunnethPulledCounit (ModuleCat.{u + 1} A) (pullback.fst f g) K ⊗ₘ
          ordinaryKunnethPulledCounit (ModuleCat.{u + 1} A) (pullback.snd f g) L)) := by
  rw [← Category.assoc, fullCoefficientTensor_left_normalized]
  change (_ ≫ (_ ⊗ₘ _)) ≫ (_ ⊗ₘ _) = _
  rw [Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  have h₁ := fullPullbackEvaluation_normalized A (pullback.fst f g) K
  have h₂ := fullPullbackEvaluation_normalized A (pullback.snd f g) L
  erw [h₁, h₂]
  rw [← tensorHom_comp_tensorHom, ← Category.assoc,
    ← Functor.leftDerivedTensorComparison_naturality_tensorHom, Category.assoc]

-- Compare the cached derived tensor structures by congruence, as in the adopted
-- projection-formula coherence proofs, rather than unfolding their construction.
open Lean Elab Tactic Meta

private theorem normalizationProofHEq
    {P Q : Prop} (p : P) (q : Q) (h : P = Q) : HEq p q := by
  cases h
  rfl

private meta partial def normalizationCongrHEq (a b : Expr) : MetaM Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← mkHEqRefl a
  if ← isProp (← inferType a) then
    let hp ← normalizationCongrHEq (← inferType a) (← inferType b)
    let e ← mkAppM ``eq_of_heq #[hp]
    return ← mkAppM ``normalizationProofHEq #[a, b, e]
  if a.getAppFn == b.getAppFn && a.getAppArgs.size == b.getAppArgs.size then
    let argsA := a.getAppArgs
    let argsB := b.getAppArgs
    let ct ← mkHCongrWithArity a.getAppFn argsA.size
    let mut ps := #[]
    for i in [:argsA.size] do
      let mut h ← normalizationCongrHEq argsA[i]! argsB[i]!
      if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
      ps := ps ++ #[argsA[i]!, argsB[i]!, h]
    let pf := mkAppN ct.proof ps
    if (← inferType pf).isHEq then return pf
    else return ← mkAppM ``heq_of_eq #[pf]
  else
    unless ← isDefEq a b do
      throwError "The full-support comparison structures are not definitionally equal"
    return ← mkHEqRefl a

private theorem fullExteriorProduct_normalized
    (A : Type (u + 1)) [CommRing A] {B X Y : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    supportedExteriorProduct A f g (𝟙 X) (𝟙 Y) K L ≫
      (fullSectionsIso A (supportedProductImmersion f g (𝟙 X) (𝟙 Y))).hom.app
        (externalProduct (ModuleCat.{u + 1} A) f g K L) =
    ((fullSectionsIso A (𝟙 X)).hom.app K ⊗ₘ (fullSectionsIso A (𝟙 Y)).hom.app L) ≫
      ordinaryGlobalKunnethMap (ModuleCat.{u + 1} A) (pullback.fst f g) (pullback.snd f g) K L := by
  dsimp only [supportedExteriorProduct, fullSectionsIso,
    ordinaryGlobalKunnethMap, ordinaryKunnethTensorMate,
    curriedTensor_map_app, curriedTensor_obj_map]
  have h := comparisonMate_congr
    (fullDerivedCoefficientIso A (supportedProductImmersion f g (𝟙 X) (𝟙 Y)))
    (derivedConstantGlobalSectionsAdjunction (ModuleCat.{u + 1} A) (pullback f g))
    (supportedCoefficientDerivedAdjunction A (supportedProductImmersion f g (𝟙 X) (𝟙 Y)))
    ((fullSectionsIso A (𝟙 X)).hom.app K ⊗ₘ (fullSectionsIso A (𝟙 Y)).hom.app L)
    _ _ (fullTensorEvaluation_normalized A f g K L)
  run_tac withMainContext do
    let t ← instantiateMVars (← getMainTarget)
    let ds := (← getLCtx).decls.toList.filterMap id
    let some d := ds.find? (fun d ↦ d.userName.eraseMacroScopes == `h) | throwError "no h"
    let q ← normalizationCongrHEq t (← instantiateMVars d.type)
    let e ← mkAppM ``eq_of_heq #[q]
    let pf ← mkAppM ``Eq.mpr #[e, d.toExpr]
    (← getMainGoal).assign pf

/-- With full supports the specified supported pairing is invertible whenever the ordinary
Künneth map is invertible.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/lem-pur-kunneth-supported.proof.md,
paragraphs 1--2
(blueprint: lem-pur-full-support-kunneth-comparison).

Proof: The coefficient quotient for an isomorphism of supports is an isomorphism, being
an adjunction unit followed by the image of the constant-pullback isomorphism. Transport
its normalized sheaf tensor comparison to signed complexes, and then through the derived
localization counits. Uniqueness of the normalized comparison identifies the derived
comparison with the ordinary constant-sheaf tensor comparison. The induced right-adjoint
isomorphism identifies the supported counits with ordinary global-sections counits.
After pulling back to both projections, tensoring the counits and transposing, the
supported pairing conjugates to ordinary Künneth by these three isomorphisms. Therefore
invertibility of ordinary Künneth implies invertibility of the specified supported pairing.
-/
theorem isIso_supportedExteriorProduct_fullSupport
    (A : Type (u + 1)) [CommRing A] {B X Y : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    [IsIso (ordinaryGlobalKunnethMap (ModuleCat.{u + 1} A)
      (pullback.fst f g) (pullback.snd f g) K L)] :
    IsIso (supportedExteriorProduct A f g (𝟙 X) (𝟙 Y) K L) := by
  have h : IsIso (supportedExteriorProduct A f g (𝟙 X) (𝟙 Y) K L ≫
      (fullSectionsIso A (supportedProductImmersion f g (𝟙 X) (𝟙 Y))).hom.app
        (externalProduct (ModuleCat.{u + 1} A) f g K L)) := by
    rw [fullExteriorProduct_normalized]
    exact ((tensorIso ((fullSectionsIso A (𝟙 X)).app K)
      ((fullSectionsIso A (𝟙 Y)).app L)) ≪≫
      asIso (ordinaryGlobalKunnethMap (ModuleCat.{u + 1} A)
        (pullback.fst f g) (pullback.snd f g) K L)).isIso_hom
  exact IsIso.of_isIso_comp_right _
    ((fullSectionsIso A (supportedProductImmersion f g (𝟙 X) (𝟙 Y))).hom.app
      (externalProduct (ModuleCat.{u + 1} A) f g K L))

end AlgebraicGeometry.Etale
