/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.Coefficient
public import WeilConjectures.WeilSheaf.Strategy3.ChangeCoefficients
public import WeilConjectures.TateTwist.IntegralReduction

/-! # Coefficient reductions whose implicit target is the duplicate coefficient object -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u
open CategoryTheory MonObj

namespace AlgebraicGeometry.ProEtale.Strategy3

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] (n : ℕ)

/-- Reduction with the new coefficient object as its explicit codomain. -/
noncomputable def finiteReduction :
    Profinite.padicIntegersRingObj.{u} ℓ E ⟶ coeffRing (PadicAlgCl.integersModPow ℓ E n) :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (Profinite.padicIntegersCondensedRingToIntegersModPow ℓ E n)

instance : IsMonHom (finiteReduction.{u} ℓ E n) := by
  unfold finiteReduction
  infer_instance

/-- The composite coefficient map, built using the same finite reduction. -/
noncomputable def compositeReduction :
    Profinite.continuousMapRingObj.{u} ℤ_[ℓ] ⟶ coeffRing (PadicAlgCl.integersModPow ℓ E n) :=
  Profinite.padicIntRingObjToPadicIntegers ℓ E ≫ finiteReduction ℓ E n

instance : IsMonHom (compositeReduction.{u} ℓ E n) := by
  unfold compositeReduction
  infer_instance

/-- Reduction on a scheme, with all implicit coefficient data inherited from `finiteReduction`. -/
noncomputable abbrev integersModPowReduction (X : Scheme.{u}) :
    condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X ⟶
      condensedRingObj (coeffRing (PadicAlgCl.integersModPow ℓ E n)) X :=
  coefficientMap (finiteReduction ℓ E n) X

lemma ringChar_coeffType :
    ringChar (coeffType.{u} (PadicAlgCl.integersModPow ℓ E n)) = ℓ ^ n :=
  ProEtale.CondensedRing.ringChar_integersModPowCoeff ℓ E n

end AlgebraicGeometry.ProEtale.Strategy3
