/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityK4NativeReadingBoundary
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

/-- The reading equation, with each coefficient-dependent datum typed at the boundary. -/
def finiteReadingEquation
    {X Y : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Spec (.of k))
    (eX : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X) ≌
      Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)))
    (eY : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) Y) ≌
      Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)))
    (pull : CondensedRing.upperStar (Profinite.integersModPowRingObj ℓ E n) g ⋙ eX.functor ≅
      eY.functor ⋙ (g)^*[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])
    (readX : eX.functor.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E n)).obj (integralTateTwistOne X ℓ E)) ≅
      ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].obj
        (Etale.tateSheaf (integersModPowCoeff.{u} ℓ E n) X))
    (readY : eY.functor.obj
        ((Mod.extendScalars (integersModPowReduction Y ℓ E n)).obj (integralTateTwistOne Y ℓ E)) ≅
      ν^*(Y)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].obj
        (Etale.tateSheaf (integersModPowCoeff.{u} ℓ E n) Y)) : Prop :=
    eX.functor.map
          ((pullIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) g).inv.app
            (integralTateTwistOne Y ℓ E)) ≫
        eX.functor.map
          ((Mod.extendScalars (integersModPowReduction X ℓ E n)).map
            (upperStarIntegralTateTwistOneIso ℓ E g f).hom) ≫
        readX.hom =
      pull.hom.app
          ((Mod.extendScalars (integersModPowReduction Y ℓ E n)).obj
            (integralTateTwistOne Y ℓ E)) ≫
        (g)^*[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          readY.hom ≫
        (comparisonUpperStarUpperStarIso
          (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g).hom.app
            (Etale.tateSheaf (integersModPowCoeff.{u} ℓ E n) Y) ≫
        ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          (Etale.upperStarTateSheafToTateSheaf (integersModPowCoeff.{u} ℓ E n) g)

/-- The native proof is consumed without changing its coefficient representation. -/
lemma finiteReadingEquation_native {X Y : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Spec (.of k)) :
    finiteReadingEquation ℓ E n g f
      (finiteCoefficientModEquivalence ℓ E n X)
      (finiteCoefficientModEquivalence ℓ E n Y)
      (upperStarFiniteCoefficientModEquivalenceIso ℓ E n g)
      (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n (g ≫ f))
      (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f) := by
  exact_mod_proofs purity_finiteCoefficientIntegralTateOneReading_pullback ℓ E n g f

/-- Interpret the equation using the original comparison and reading constructors. -/
lemma finiteReadingEquation_original {X Y : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Spec (.of k)) :
    finiteReadingEquation ℓ E n g f
      (ProEtale.finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n))
      (ProEtale.finiteCoefficientModEquivalence Y (PadicAlgCl.integersModPow ℓ E n))
      (ProEtale.upperStarFiniteCoefficientModEquivalenceIso g (PadicAlgCl.integersModPow ℓ E n))
      (ProEtale.finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n (g ≫ f))
      (ProEtale.finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f) := by
  have h := finiteReadingEquation_native ℓ E n g f
  simp only [finiteCoefficientModEquivalence_eq,
    upperStarFiniteCoefficientModEquivalenceIso_eq,
    finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso_eq] at h
  exact_mod_proofs h

end AlgebraicGeometry.ProEtale.K4Native
