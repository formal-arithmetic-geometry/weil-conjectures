/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityK4NativeFiniteTateOneReading
public import WeilConjectures.WeilSheaf.SmoothPurityFiniteTateLineReading
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

/-- The native coefficient equivalence agrees with the existing implementation. -/
lemma finiteCoefficientModEquivalence_eq (X : Scheme.{u}) :
    finiteCoefficientModEquivalence ℓ E n X =
      ProEtale.finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n) := rfl

lemma lowerStarFiniteCoefficientModEquivalenceIso_eq {X Y : Scheme.{u}} (g : X ⟶ Y) :
    lowerStarFiniteCoefficientModEquivalenceIso ℓ E n g =
      ProEtale.lowerStarFiniteCoefficientModEquivalenceIso g
        (PadicAlgCl.integersModPow ℓ E n) := rfl

lemma upperStarFiniteCoefficientModEquivalenceIso_eq {X Y : Scheme.{u}} (g : X ⟶ Y) :
    upperStarFiniteCoefficientModEquivalenceIso ℓ E n g =
      ProEtale.upperStarFiniteCoefficientModEquivalenceIso g
        (PadicAlgCl.integersModPow ℓ E n) := rfl

lemma comparisonUpperStarFreeIso_eq (X : Scheme.{u}) :
    comparisonUpperStarFreeIso ℓ E n X =
      ProEtale.comparisonUpperStarFreeIso (PadicAlgCl.integersModPow ℓ E n) X := rfl

lemma finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso_eq
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f =
      ProEtale.finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f := rfl

end AlgebraicGeometry.ProEtale.K4Native
