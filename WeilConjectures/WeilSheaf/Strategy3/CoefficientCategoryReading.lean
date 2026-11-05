/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.CoefficientCategory
public import WeilConjectures.WeilSheaf.Strategy3.IntegralTateReading

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3.K4Coefficient

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (n : ℕ) {k : Type u} [Field k] [NeZero (ℓ : k)]

noncomputable def tateObject (X : Scheme.{u}) : Object (PadicAlgCl.integersModPow ℓ E n) X :=
  ⟨ν^*(X)[ModuleCat.{u + 1} (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n))].obj
    (Etale.tateSheaf (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n)) X)⟩

noncomputable def integralReadingIso {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    (reading (PadicAlgCl.integersModPow ℓ E n) X).obj
      ((Mod.extendScalars (integersModPowReduction ℓ E n X)).obj
        (integralTateTwistOne X ℓ E)) ≅ tateObject ℓ E n X where
  hom := (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f).hom
  inv := (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f).inv
  hom_inv_id := (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso
    ℓ E n f).hom_inv_id
  inv_hom_id := (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso
    ℓ E n f).inv_hom_id

noncomputable def tatePullback {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (upperStar (PadicAlgCl.integersModPow ℓ E n) g).obj (tateObject ℓ E n Y) ⟶
      tateObject ℓ E n X :=
  (comparisonUpperStarUpperStarIso
    (ModuleCat.{u + 1} (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n))) g).hom.app
      (Etale.tateSheaf (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n)) Y) ≫
    ν^*(X)[ModuleCat.{u + 1} (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n))].map
      (Etale.upperStarTateSheafToTateSheaf (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n)) g)

/-- The concrete integral reading calculation, in the dedicated coefficient category. -/
lemma integralReading_pullback {X Y : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Spec (.of k)) :
    (reading (PadicAlgCl.integersModPow ℓ E n) X).map
        ((pullIso (finiteReduction ℓ E n) g).inv.app (integralTateTwistOne Y ℓ E)) ≫
      (reading (PadicAlgCl.integersModPow ℓ E n) X).map
        ((Mod.extendScalars (integersModPowReduction ℓ E n X)).map
          (upperStarIntegralTateTwistOneIso ℓ E g f).hom) ≫
      (integralReadingIso ℓ E n (g ≫ f)).hom =
    (readingPullbackIso (PadicAlgCl.integersModPow ℓ E n) g).hom.app
        ((Mod.extendScalars (integersModPowReduction ℓ E n Y)).obj
          (integralTateTwistOne Y ℓ E)) ≫
      (upperStar (PadicAlgCl.integersModPow ℓ E n) g).map
        (integralReadingIso ℓ E n f).hom ≫ tatePullback ℓ E n g := by
  exact Strategy3.purity_finiteCoefficientIntegralTateOneReading_pullback ℓ E n g f

/-- Applying realization once is sufficient to export any equation from this category. -/
lemma realize_equation {X : Scheme.{u}}
    {A B : Object (PadicAlgCl.integersModPow ℓ E n) X} {f g : A ⟶ B} (h : f = g) :
    (realize (PadicAlgCl.integersModPow ℓ E n) X).map f =
      (realize (PadicAlgCl.integersModPow ℓ E n) X).map g :=
  congrArg ((realize (PadicAlgCl.integersModPow ℓ E n) X).map) h

#print axioms integralReading_pullback

end AlgebraicGeometry.ProEtale.Strategy3.K4Coefficient
