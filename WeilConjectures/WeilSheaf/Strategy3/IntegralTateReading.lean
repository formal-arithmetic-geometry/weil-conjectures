/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.TateReading
public import WeilConjectures.WeilSheaf.SmoothPurityReadingComposition
public import WeilConjectures.WeilSheaf.Strategy3.IntegralReductionPullback
import WeilConjectures.Tactic.ExactModProofs

/-! # The finite étale reading of the integral one-twist datum -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (n : ℕ) {k : Type u} [Field k] [NeZero (ℓ : k)]

/-- The finite integral Tate reading, assembled entirely from the duplicate infrastructure. -/
noncomputable def finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n)).functor.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E n)).obj
          (integralTateTwistOne X ℓ E)) ≅
      ν^*(X)[ModuleCat.{u + 1} (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n))].obj
        (Etale.tateSheaf (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n)) X) :=
  (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n)).functor.mapIso
      (extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n f) ≪≫
    purityFiniteRootTateReadingIso (PadicAlgCl.integersModPow ℓ E n) (ℓ ^ n)
      (pow_pos (Fact.out : ℓ.Prime).pos n)
      (ProEtale.CondensedRing.ringChar_integersModPowCoeff ℓ E n) X
      (isUnit_natCast_pow_of_neZero ℓ n f)

/-- Factor the existing integral Tate reading through its finite free-root line. -/
lemma purity_finiteCoefficientIntegralTateOneReading_eq
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f =
      (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n)).functor.mapIso
          (extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n f) ≪≫
        purityFiniteRootTateReadingIso (PadicAlgCl.integersModPow ℓ E n) (ℓ ^ n)
          (pow_pos (Fact.out : ℓ.Prime).pos n) (ProEtale.CondensedRing.ringChar_integersModPowCoeff ℓ E n)
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
        (g)^*[ModuleCat.{u + 1} (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n))].map
          (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f).hom ≫
        (comparisonUpperStarUpperStarIso
          (ModuleCat.{u + 1} (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n))) g).hom.app
            (Etale.tateSheaf (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n)) Y) ≫
        ν^*(X)[ModuleCat.{u + 1} (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n))].map
          (Etale.upperStarTateSheafToTateSheaf (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n)) g) := by
  have hzero : ((ℓ ^ n : ℕ) : PadicAlgCl.integersModPow ℓ E n) = 0 := by
    exact (PadicAlgCl.natCast_eq_zero_integersModPow_iff ℓ E n (ℓ ^ n)).mpr dvd_rfl
  have hf := purityFiniteRootTateReadingIso_pullback
    (PadicAlgCl.integersModPow ℓ E n) (ℓ ^ n) (pow_pos (Fact.out : ℓ.Prime).pos n)
    (ProEtale.CondensedRing.ringChar_integersModPowCoeff ℓ E n) hzero g
    (isUnit_natCast_pow_of_neZero ℓ n f) (isUnit_natCast_pow_of_neZero ℓ n (g ≫ f))
  have hr := upperStarIntegralTateTwistOneIso_hom_comp_reduction ℓ E g f n
  simp only [purityTateRootPullbackIso,
    upperStarRootsOfUnitySheafIsoOfInvertible_hom] at hr
  have h := purity_reading_composition_named
    (Strategy3.upperStar (coeffRing (PadicAlgCl.integersModPow ℓ E n)) g)
    (finiteCoefficientModEquivalence Y (PadicAlgCl.integersModPow ℓ E n)).functor
    (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n)).functor
    (g)^*[ModuleCat.{u + 1} (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n))]
    (upperStarFiniteCoefficientModEquivalenceIso g (PadicAlgCl.integersModPow ℓ E n))
    (Mod.extendScalars (coefficientMap
      (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) Y))
    (Strategy3.upperStar (Profinite.padicIntegersRingObj ℓ E) g ⋙
      Mod.extendScalars (coefficientMap
        (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) X))
    (pullIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) g).inv
    (integralTateTwistOne Y ℓ E)
    ((Mod.extendScalars (integersModPowReduction X ℓ E n)).map
      (upperStarIntegralTateTwistOneIso ℓ E g f).hom)
    (extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n (g ≫ f))
    (extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n f)
    ((freeFunctorCompUpperStarIso (coeffRing (PadicAlgCl.integersModPow ℓ E n)) g).hom.app
      (rootsOfUnitySheaf Y (ℓ ^ n)))
    ((Mod.freeFunctor (condensedRingObj (coeffRing (PadicAlgCl.integersModPow ℓ E n)) X)).map
      (upperStarRootsOfUnitySheafHom g (ℓ ^ n)))
    (purityFiniteRootTateReadingIso (PadicAlgCl.integersModPow ℓ E n) (ℓ ^ n)
      (pow_pos (Fact.out : ℓ.Prime).pos n) (ProEtale.CondensedRing.ringChar_integersModPowCoeff ℓ E n)
      X (isUnit_natCast_pow_of_neZero ℓ n (g ≫ f)))
    (purityFiniteRootTateReadingIso (PadicAlgCl.integersModPow ℓ E n) (ℓ ^ n)
      (pow_pos (Fact.out : ℓ.Prime).pos n) (ProEtale.CondensedRing.ringChar_integersModPowCoeff ℓ E n)
      Y (isUnit_natCast_pow_of_neZero ℓ n f))
    ((comparisonUpperStarUpperStarIso
      (ModuleCat.{u + 1} (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n))) g).hom.app
        (Etale.tateSheaf (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n)) Y) ≫
      ν^*(X)[ModuleCat.{u + 1} (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n))].map
        (Etale.upperStarTateSheafToTateSheaf (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n)) g))
    (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n (g ≫ f))
    (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f)
    (purity_finiteCoefficientIntegralTateOneReading_eq ℓ E n (g ≫ f))
    (purity_finiteCoefficientIntegralTateOneReading_eq ℓ E n f)
    (by
      dsimp only [Functor.comp_obj, Functor.comp_map, integersModPowReduction] at hr ⊢
      exact_mod_proofs hr)
    (by
      dsimp only [Functor.comp_obj, Functor.comp_map] at hf ⊢
      exact_mod_proofs hf)
  dsimp only [Functor.comp_obj, Functor.comp_map, integersModPowReduction] at h ⊢
  exact_mod_proofs h

end AlgebraicGeometry.ProEtale.Strategy3
