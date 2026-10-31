/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalRealizationData

import WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationPullbackComparison
import WeilConjectures.AlgebraicGeometry.ContinuousRational.RationalContinuousOrdinaryPullback
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationNaturalIso
import WeilConjectures.AlgebraicGeometry.ContinuousSlice.ContinuousCoefficientSliceNormalization

/-! # Transport of normalized rational pullback comparisons

Source: Bhatt--Scholze, Remark 6.8.15; Stacks 03EL, 06YY, 099N
(blueprint: lem-per-rational-continuous-pullback-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u r a b a' b'
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.ContinuousRational

private def transportIntegral
    (R : Type r) [CommRing R] (p : R)
    {C : Type a} [Category.{b} C] [Preadditive C] [Linear R C]
    {D : Type a'} [Category.{b'} D] [Preadditive D] [Linear R D]
    (F : C ⥤ D) [F.Additive] [F.Linear R] :
    ScalarLocalization.localization R C p ⋙ ScalarLocalization.transport R p F ≅
      F ⋙ ScalarLocalization.localization R D p :=
  NatIso.ofComponents (fun _ ↦ { hom := 𝟙 _, inv := 𝟙 _ }) (by
    intro X Y f
    dsimp only [Functor.comp_map, ScalarLocalization.localization,
      ScalarLocalization.transport, Iso.refl_hom]
    simp only [Category.comp_id, Category.id_comp,
      ScalarLocalization.transportHom, LinearMap.baseChange_tmul]
    rfl)

private theorem normalizedCoefficient_unique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (c d : (adicTowerInverseImage g).obj (rationalCoefficientSheaf l Y E) ⟶
      rationalCoefficientSheaf l X E)
    (hc : rationalCoefficientRestrictionNormalized l E g c)
    (hd : rationalCoefficientRestrictionNormalized l E g d) : c = d := by
  let := coefficientExtensionNormedField l E
  apply ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).injective
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  apply ContinuousMap.ext
  intro x
  exact (hc U.unop s x).trans (hd U.unop s x).symm

private theorem normalizedPull_special
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (c : (adicTowerInverseImage g).obj (rationalCoefficientSheaf l Y.scheme E) ⟶
      rationalCoefficientSheaf l X.scheme E)
    (hc : rationalCoefficientRestrictionNormalized l E g c)
    (hg : Etale g ∨ IsImmersion g) :
    IsIso c ∧ PreservesFiniteLimits (modulePull g c) ∧
      PreservesFiniteColimits (modulePull g c) := by
  obtain ⟨a, _, ⟨e⟩, _⟩ :=
    (ContinuousSlice.continuous_coefficient_slice_normalization l E).2.2.1
      Y.scheme X.scheme Y.dimension X.dimension Y.prime_unit X.prime_unit g hg
  have h := normalizedCoefficient_unique l E g c a.rational.hom hc a.rational_normalized
  subst c
  refine ⟨inferInstance, ?_, ?_⟩
  · exact preservesFiniteLimits_of_natIso e.ordinary.symm
  · exact preservesFiniteColimits_of_natIso e.ordinary.symm

private theorem completedPreservation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme) :
    (∀ K : PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E),
      PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)
        ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K.obj)) ∧
    ∀ K : PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E),
      IsIso ((pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).app K.obj) := by
  obtain ⟨sX⟩ := rationalModuleRealizationFunctor l E X.scheme
  obtain ⟨sY⟩ := rationalModuleRealizationFunctor l E Y.scheme
  obtain ⟨r⟩ := rationalRealizationPullbackComparison l E g sX sY
  obtain ⟨e, he, _⟩ := pbcActualCompletedPullback_tower (pbcIntegralDatum l E) g
  have := (pbcIntegralUniformComplete_isTriangulated l E X.scheme
    X.dimension X.prime_unit).1
  constructor
  · intro K
    exact ObjectProperty.prop_of_iso _ (e.app ⟨K.obj, K.property.1⟩)
      (r.integral.completed_mem K)
  · intro K
    rw [← he ⟨K.obj, K.property.1⟩]
    have := r.integral.unit_isIso K
    infer_instance

private theorem completedComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (aX : At l E X) (aY : At l E Y)
    (c : (adicTowerInverseImage g).obj (rationalCoefficientSheaf l Y.scheme E) ⟶
      rationalCoefficientSheaf l X.scheme E)
    (b : pbcDerivedExtend (aY.integralIso.hom ≫ aY.inclusion) ⋙ derivedPull g c ≅
      pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
        pbcDerivedExtend (aX.integralIso.hom ≫ aX.inclusion))
    (hm : ∀ K : PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E),
      PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)
        ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K.obj))
    (hu : ∀ K : PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E),
      IsIso ((pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).app K.obj)) :
    ∃ e : rawPull l E g hm ⋙ aX.J ≅ aY.J ⋙ derivedPull g c,
      ∀ K : PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E),
        b.hom.app K.obj ≫
            (pbcDerivedExtend (aX.integralIso.hom ≫ aX.inclusion)).map
              ((pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).app K.obj) ≫
            aX.integral.inv.app ((integralPull l E g hm).obj K) =
          (derivedPull g c).map (aY.integral.inv.app K) ≫
            e.inv.app ((pbcRationalization Y.scheme (pbcIntegralDatum l E)
              (pbcUniformizer l E)).obj K) := by
  let QX := pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)
  let QY := pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)
  let IX := ObjectProperty.ι (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E))
  let IY := ObjectProperty.ι (PbcIsBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E))
  let P := integralPull l E g hm
  let DX := pbcDerivedExtend (aX.integralIso.hom ≫ aX.inclusion)
  let DY := pbcDerivedExtend (aY.integralIso.hom ≫ aY.inclusion)
  let D := derivedPull g c
  let L := pbcActualDerivedPull g (pbcIntegralDatum l E)
  let eraw : QY ⋙ rawPull l E g hm ≅ P ⋙ QX :=
    transportIntegral (PbcIntegralRing l E) (pbcUniformizer l E) P
  let completion : IY ⋙ L ≅ P ⋙ IX :=
    NatIso.ofComponents (fun K ↦ by
      have := hu K
      exact asIso ((pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).app K.obj))
      (by
        intro K N f
        change L.map f.hom ≫
            (pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).app N.obj =
          (pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).app K.obj ≫
            (pbcActualCompletedPull g (pbcIntegralDatum l E)).map f.hom
        exact (pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).naturality f.hom)
  let e : QY ⋙ (rawPull l E g hm ⋙ aX.J) ≅ QY ⋙ (aY.J ⋙ D) :=
    (Functor.associator QY _ _).symm ≪≫
      Functor.isoWhiskerRight eraw aX.J ≪≫ Functor.associator P QX aX.J ≪≫
      Functor.isoWhiskerLeft P aX.integral ≪≫ (Functor.associator P IX DX).symm ≪≫
      Functor.isoWhiskerRight completion.symm DX ≪≫ Functor.associator IY L DX ≪≫
      Functor.isoWhiskerLeft IY b.symm ≪≫ (Functor.associator IY DY D).symm ≪≫
      Functor.isoWhiskerRight aY.integral.symm D ≪≫ Functor.associator QY aY.J D
  obtain ⟨d, hd, _⟩ := ScalarLocalization.naturalIso_of_integral (PbcIntegralRing l E)
    (PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E))
    (pbcUniformizer l E) (rawPull l E g hm ⋙ aX.J) (aY.J ⋙ D) e
  refine ⟨d, ?_⟩
  intro K
  have hdk : d.app (QY.obj K) = e.app K := Iso.ext (hd K)
  have hdki : d.inv.app (QY.obj K) = e.inv.app K := congrArg Iso.inv hdk
  rw [hdki]
  simp only [e, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, eraw, transportIntegral,
    NatIso.ofComponents_inv_app,
    NatIso.ofComponents_hom_app,
    completion, Category.id_comp, Category.comp_id,
    Category.assoc, asIso_hom]
  rw [← D.map_comp_assoc, Iso.inv_hom_id_app, D.map_id, Category.id_comp]
  erw [aX.J.map_id, Category.comp_id]
  rfl

/-- Normalize the ordinary tensor factor and completion presentation of the rational
pullback comparison, retaining the specified realization integral comparisons.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks 03EL, 06YY, 099N
(blueprint: lem-per-rational-continuous-pullback-transport).

Proof: obtain the ordinary coefficient, normalized universal counit and tensor
balance from rationalContinuousOrdinaryPullback. Choose raw module realizations and
apply the existing rational pullback comparison for strict completed membership and
invertibility of its specified unit. Transfer these through the unit-compatible
strict-tower/reflector comparison; the integral predicate is closed under isomorphisms.
The actual completion unit is consequently an isomorphism on the integral category.
Compose its inverse with the two specified integral realization isomorphisms and the
ordinary ambient balance. Raw pullback commutes with rationalization by tensoring
integral arrows with one. Categorical localization extends the resulting integral
natural isomorphism to raw rational objects. Its component equation and the inverse
identities give the required completion-unit equation. Finally, normalized coefficient
maps are unique by pointwise extensionality after the sheaf adjunction. For etale maps
and immersions identify the coefficient map with the one in continuous slice
normalization and transfer exactness across its ordinary comparison. -/
theorem rationalContinuousPullbackTransport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (aX : At l E X) (aY : At l E Y) : Nonempty (Along l E g aX aY) := by
  obtain ⟨o⟩ := rationalContinuousOrdinaryPullback l E g aX aY
  obtain ⟨hm, hu⟩ := completedPreservation l E g
  obtain ⟨e, he⟩ := completedComparison l E g aX aY o.coefficient o.ambient hm hu
  exact ⟨{
    coefficient := o.coefficient
    normalized := o.normalized
    square := o.square
    ordinaryAdditive := o.ordinaryAdditive
    counit := o.counit
    normalized_counit := o.normalized_counit
    universal := o.universal
    computes := o.computes
    balance := o.balance
    balance_sections := o.balance_sections
    ambient := o.ambient
    balanceComplex := o.balanceComplex
    balanceComplex_components := o.balanceComplex_components
    ambient_normalization := o.ambient_normalization
    integral_mem := hm
    comparison := e
    completion_unit := he
    special := normalizedPull_special l E g o.coefficient o.normalized }⟩

end AlgebraicGeometry.Scheme.ContinuousRational
