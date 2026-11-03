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

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

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

end AlgebraicGeometry.Scheme.ContinuousRational
