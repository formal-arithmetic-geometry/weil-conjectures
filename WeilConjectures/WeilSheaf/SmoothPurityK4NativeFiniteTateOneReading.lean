/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityK4NativeFiniteTateLineReading
public import WeilConjectures.WeilSheaf.SmoothPurityReadingComposition
public import WeilConjectures.WeilSheaf.SmoothPurityIntegralTateReductionPullback
import WeilConjectures.Tactic.ExactModProofs

/-! # The finite étale reading of the integral one-twist datum -/

set_option profiler true
set_option profiler.threshold 1

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.K4Native

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (n : ℕ) {k : Type u} [Field k] [NeZero (ℓ : k)]

/-- Integral Tate reading constructed in the native coefficient vocabulary. -/
noncomputable def finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    (finiteCoefficientModEquivalence ℓ E n X).functor.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E n)).obj (integralTateTwistOne X ℓ E)) ≅
      ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].obj
        (Etale.tateSheaf (integersModPowCoeff.{u} ℓ E n) X) :=
  (finiteCoefficientModEquivalence ℓ E n X).functor.mapIso
      (extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n f) ≪≫
    purityFiniteRootTateReadingIso ℓ E n (ℓ ^ n) (pow_pos (Fact.out : ℓ.Prime).pos n)
      (ringChar_integersModPowCoeff ℓ E n) X (isUnit_natCast_pow_of_neZero ℓ n f)

/-- Factor the existing integral Tate reading through its finite free-root line. -/
lemma purity_finiteCoefficientIntegralTateOneReading_eq
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f =
      (finiteCoefficientModEquivalence ℓ E n X).functor.mapIso
          (extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n f) ≪≫
        purityFiniteRootTateReadingIso ℓ E n (ℓ ^ n)
          (pow_pos (Fact.out : ℓ.Prime).pos n) (ringChar_integersModPowCoeff ℓ E n)
          X (isUnit_natCast_pow_of_neZero ℓ n f) := by
  rfl

/-- The actual finite-coefficient reading of the integral Tate line preserves its
geometric pullback datum. -/
lemma purity_finiteCoefficientIntegralTateOneReading_pullback
    {X Y : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Spec (.of k)) :
    (finiteCoefficientModEquivalence ℓ E n X).functor.map
          ((pullIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) g).inv.app
            (integralTateTwistOne Y ℓ E)) ≫
        (finiteCoefficientModEquivalence ℓ E n X).functor.map
          ((Mod.extendScalars (integersModPowReduction X ℓ E n)).map
            (upperStarIntegralTateTwistOneIso ℓ E g f).hom) ≫
        (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso
          ℓ E n (g ≫ f)).hom =
      (upperStarFiniteCoefficientModEquivalenceIso ℓ E n g).hom.app
          ((Mod.extendScalars (integersModPowReduction Y ℓ E n)).obj
            (integralTateTwistOne Y ℓ E)) ≫
        (g)^*[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f).hom ≫
        (comparisonUpperStarUpperStarIso
          (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g).hom.app
            (Etale.tateSheaf (integersModPowCoeff.{u} ℓ E n) Y) ≫
        ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          (Etale.upperStarTateSheafToTateSheaf (integersModPowCoeff.{u} ℓ E n) g) := by
  have hzero : ((ℓ ^ n : ℕ) : PadicAlgCl.integersModPow ℓ E n) = 0 := by
    exact (PadicAlgCl.natCast_eq_zero_integersModPow_iff ℓ E n (ℓ ^ n)).mpr dvd_rfl
  have hf := purityFiniteRootTateReadingIso_pullback
    ℓ E n (ℓ ^ n) (pow_pos (Fact.out : ℓ.Prime).pos n)
    (ringChar_integersModPowCoeff ℓ E n) hzero g
    (isUnit_natCast_pow_of_neZero ℓ n f) (isUnit_natCast_pow_of_neZero ℓ n (g ≫ f))
  have hr := upperStarIntegralTateTwistOneIso_hom_comp_reduction ℓ E g f n
  simp only [purityTateRootPullbackIso,
    upperStarRootsOfUnitySheafIsoOfInvertible_hom] at hr
  have h := purity_reading_composition_named
    (CondensedRing.upperStar (Profinite.integersModPowRingObj ℓ E n) g)
    (finiteCoefficientModEquivalence ℓ E n Y).functor
    (finiteCoefficientModEquivalence ℓ E n X).functor
    (g)^*[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)]
    (upperStarFiniteCoefficientModEquivalenceIso ℓ E n g)
    (Mod.extendScalars (coefficientMap
      (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) Y))
    (CondensedRing.upperStar (Profinite.padicIntegersRingObj ℓ E) g ⋙
      Mod.extendScalars (coefficientMap
        (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) X))
    (pullIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) g).inv
    (integralTateTwistOne Y ℓ E)
    ((Mod.extendScalars (integersModPowReduction X ℓ E n)).map
      (upperStarIntegralTateTwistOneIso ℓ E g f).hom)
    (extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n (g ≫ f))
    (extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n f)
    ((freeFunctorCompUpperStarIso (Profinite.integersModPowRingObj ℓ E n) g).hom.app
      (rootsOfUnitySheaf Y (ℓ ^ n)))
    ((Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)).map
      (upperStarRootsOfUnitySheafHom g (ℓ ^ n)))
    (purityFiniteRootTateReadingIso ℓ E n (ℓ ^ n)
      (pow_pos (Fact.out : ℓ.Prime).pos n) (ringChar_integersModPowCoeff ℓ E n)
      X (isUnit_natCast_pow_of_neZero ℓ n (g ≫ f)))
    (purityFiniteRootTateReadingIso ℓ E n (ℓ ^ n)
      (pow_pos (Fact.out : ℓ.Prime).pos n) (ringChar_integersModPowCoeff ℓ E n)
      Y (isUnit_natCast_pow_of_neZero ℓ n f))
    ((comparisonUpperStarUpperStarIso
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g).hom.app
        (Etale.tateSheaf (integersModPowCoeff.{u} ℓ E n) Y) ≫
      ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
        (Etale.upperStarTateSheafToTateSheaf (integersModPowCoeff.{u} ℓ E n) g))
    (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n (g ≫ f))
    (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f)
    (purity_finiteCoefficientIntegralTateOneReading_eq ℓ E n (g ≫ f))
    (purity_finiteCoefficientIntegralTateOneReading_eq ℓ E n f)
    (by
      dsimp +instances only [Functor.comp_obj, Functor.comp_map, integersModPowReduction] at hr ⊢
      exact_mod_proofs hr)
    (by
      dsimp +instances only [Functor.comp_obj, Functor.comp_map] at hf ⊢
      exact_mod_proofs hf)
  dsimp +instances only [Functor.comp_obj, Functor.comp_map, integersModPowReduction] at h ⊢
  exact_mod_proofs h


end AlgebraicGeometry.ProEtale.K4Native
