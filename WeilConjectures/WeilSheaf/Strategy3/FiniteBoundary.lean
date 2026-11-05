/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.TateReading
public import WeilConjectures.WeilSheaf.Strategy3.PullbackBoundary

/-! # Separately checked boundary identifications for the duplicate finite reading -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

lemma finiteCoefficientModEquivalence_eq (X : Scheme.{u}) :
    finiteCoefficientModEquivalence X T = ProEtale.finiteCoefficientModEquivalence X T := by
  rfl

lemma lowerStarFiniteCoefficientModEquivalenceIso_eq {X Y : Scheme.{u}} (g : X ⟶ Y) :
    lowerStarFiniteCoefficientModEquivalenceIso g T =
      ProEtale.lowerStarFiniteCoefficientModEquivalenceIso g T := by
  rfl

lemma upperStarFiniteCoefficientModEquivalenceIso_eq {X Y : Scheme.{u}} (g : X ⟶ Y) :
    upperStarFiniteCoefficientModEquivalenceIso g T =
      ProEtale.upperStarFiniteCoefficientModEquivalenceIso g T := by
  unfold upperStarFiniteCoefficientModEquivalenceIso
    ProEtale.upperStarFiniteCoefficientModEquivalenceIso
  simp only [upperStarLowerStarAdjunction_eq, finiteCoefficientModEquivalence_eq,
    lowerStarFiniteCoefficientModEquivalenceIso_eq]

lemma finiteCoefficientModEquivalenceFreeRootsOfUnityIso_eq
    (X : Scheme.{u}) (N : ℕ) (hN : 0 < N) (hX : IsUnit (N : Γ(X, ⊤))) :
    finiteCoefficientModEquivalenceFreeRootsOfUnityIso X N T hN hX =
      ProEtale.finiteCoefficientModEquivalenceFreeRootsOfUnityIso X N T hN hX := by
  rfl

lemma purityFiniteRootTateReadingIso_eq
    (N : ℕ) (hN : 0 < N) (hchar : ringChar (coeffType.{u} T) = N)
    (X : Scheme.{u}) (hX : IsUnit (N : Γ(X, ⊤))) :
    purityFiniteRootTateReadingIso T N hN hchar X hX =
      ProEtale.purityFiniteRootTateReadingIso T N hN hchar X hX := by
  rfl

end AlgebraicGeometry.ProEtale.Strategy3
