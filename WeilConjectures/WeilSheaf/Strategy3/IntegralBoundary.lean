/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.IntegralTateReading
public import WeilConjectures.WeilSheaf.Strategy3.FiniteBoundary

/-! # Iso-level boundary from the duplicate integral reading to the upstream API -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3
open Scheme

lemma pullIso_eq
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    pullIso a g = CondensedRing.pullIso a g := by
  rfl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  {k : Type u} [Field k] [NeZero (ℓ : k)]

lemma upperStarIntegralTateTwistOneIso_eq {X Y : Scheme.{u}}
    (g : X ⟶ Y) (f : Y ⟶ Spec (.of k)) :
    upperStarIntegralTateTwistOneIso ℓ E g f =
      ProEtale.upperStarIntegralTateTwistOneIso ℓ E g f := by
  rfl

lemma extendScalarsIntegralTateTwistOneIntegersModPowIso_eq (n : ℕ)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n f =
      ProEtale.extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n f := by
  rfl

variable [FiniteDimensional ℚ_[ℓ] E]

lemma finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso_eq (n : ℕ)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f =
      ProEtale.finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f := by
  rfl

end AlgebraicGeometry.ProEtale.Strategy3
