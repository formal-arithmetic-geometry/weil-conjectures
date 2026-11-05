/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.IntegralBoundary
import WeilConjectures.Tactic.ExactModProofs

/-! # The original finite Tate reading statement, from the independent implementation -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (n : ℕ) {k : Type u} [Field k] [NeZero (ℓ : k)]

theorem purity_finiteCoefficientIntegralTateOneReading_pullback_original
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
  have h := Strategy3.purity_finiteCoefficientIntegralTateOneReading_pullback ℓ E n g f
  simp only [Strategy3.finiteCoefficientModEquivalence_eq,
    Strategy3.pullIso_eq, Strategy3.upperStarIntegralTateTwistOneIso_eq,
    Strategy3.finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso_eq,
    Strategy3.upperStarFiniteCoefficientModEquivalenceIso_eq] at h
  dsimp only [Strategy3.coeffType, Strategy3.coeffRing, Strategy3.finiteReduction,
    Strategy3.integersModPowReduction, Strategy3.coefficientMap,
    integersModPowCoeff, Profinite.integersModPowRingObj,
    integersModPowReduction, Profinite.padicIntegersRingObjToIntegersModPow,
    Functor.comp_obj, Functor.comp_map] at h ⊢
  exact_mod_proofs h

#print axioms purity_finiteCoefficientIntegralTateOneReading_pullback_original

end AlgebraicGeometry.ProEtale
