/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityK4NativeReadingEquation
import WeilConjectures.Tactic.ExactModProofs

/-! # The finite étale reading of the integral one-twist datum -/

set_option profiler true
set_option profiler.threshold 1

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
    K4Native.finiteReadingEquation ℓ E n g f
      (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n))
      (finiteCoefficientModEquivalence Y (PadicAlgCl.integersModPow ℓ E n))
      (upperStarFiniteCoefficientModEquivalenceIso g (PadicAlgCl.integersModPow ℓ E n))
      (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n (g ≫ f))
      (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f) := by
  exact K4Native.finiteReadingEquation_original ℓ E n g f


/-- The actual finite-coefficient reading of the integral Tate line preserves its
geometric pullback datum. -/
lemma purity_finiteCoefficientIntegralTateOneReading_pullback_exact
    {X Y : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Spec (.of k)) :
    K4Native.finiteReadingEquation ℓ E n g f
      (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n))
      (finiteCoefficientModEquivalence Y (PadicAlgCl.integersModPow ℓ E n))
      (upperStarFiniteCoefficientModEquivalenceIso g (PadicAlgCl.integersModPow ℓ E n))
      (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n (g ≫ f))
      (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f) := by
  exact purity_finiteCoefficientIntegralTateOneReading_pullback ℓ E n g f

end AlgebraicGeometry.ProEtale
