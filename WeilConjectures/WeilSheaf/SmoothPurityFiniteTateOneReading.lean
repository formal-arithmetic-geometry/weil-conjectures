/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFiniteTateLineReading
public import WeilConjectures.WeilSheaf.SmoothPurityIntegralTateReductionPullback

/-! # The finite étale reading of the integral one-twist datum -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (n : ℕ) {k : Type u} [Field k] [NeZero (ℓ : k)]

/-- Factor the existing integral Tate reading through its finite free-root line. -/
lemma purity_finiteCoefficientIntegralTateOneReading_eq
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f =
      (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n)).functor.mapIso
          (extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n f) ≪≫
        purityFiniteRootTateReadingIso (PadicAlgCl.integersModPow ℓ E n) (ℓ ^ n)
          (pow_pos (Fact.out : ℓ.Prime).pos n) (ringChar_integersModPowCoeff ℓ E n)
          X (isUnit_natCast_pow_of_neZero ℓ n f) := by
  rfl

/-- The actual finite-coefficient reading of the integral Tate line preserves its
geometric pullback datum. -/
lemma purity_finiteCoefficientIntegralTateOneReading_pullback
    {X Y : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Spec (.of k)) :
    (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n)).functor.map
          ((pullIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) g).inv.app
            (integralTateTwistOne Y ℓ E)) ≫
        (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n)).functor.map
          ((Mod.extendScalars (integersModPowReduction X ℓ E n)).map
            (upperStarIntegralTateTwistOneIso ℓ E g f).hom) ≫
        (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso
          ℓ E n (g ≫ f)).hom =
      (upperStarFiniteCoefficientModEquivalenceIso g
        (PadicAlgCl.integersModPow ℓ E n)).hom.app
          ((Mod.extendScalars (integersModPowReduction Y ℓ E n)).obj
            (integralTateTwistOne Y ℓ E)) ≫
        (g)^*[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f).hom ≫
        (comparisonUpperStarUpperStarIso
          (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g).hom.app
            (Etale.tateSheaf (integersModPowCoeff.{u} ℓ E n) Y) ≫
        ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          (Etale.upperStarTateSheafToTateSheaf (integersModPowCoeff.{u} ℓ E n) g) := by
  have hr := congrArg
    (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n)).functor.map
    (upperStarIntegralTateTwistOneIso_hom_comp_reduction ℓ E g f n)
  have hzero : ((ℓ ^ n : ℕ) : PadicAlgCl.integersModPow ℓ E n) = 0 := by
    exact (PadicAlgCl.natCast_eq_zero_integersModPow_iff ℓ E n (ℓ ^ n)).mpr dvd_rfl
  have hf := purityFiniteRootTateReadingIso_pullback
    (PadicAlgCl.integersModPow ℓ E n) (ℓ ^ n) (pow_pos (Fact.out : ℓ.Prime).pos n)
    (ringChar_integersModPowCoeff ℓ E n) hzero g
    (isUnit_natCast_pow_of_neZero ℓ n f) (isUnit_natCast_pow_of_neZero ℓ n (g ≫ f))
  have hn := (upperStarFiniteCoefficientModEquivalenceIso g
    (PadicAlgCl.integersModPow ℓ E n)).hom.naturality
      (extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n f).hom
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Functor.map_comp, Category.assoc, purityTateRootPullbackIso,
    upperStarRootsOfUnitySheafIsoOfInvertible_hom] at hr
  simp only [purity_finiteCoefficientIntegralTateOneReading_eq, Iso.trans_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hr, reassoc_of% hf, reassoc_of% hn]

end AlgebraicGeometry.ProEtale
