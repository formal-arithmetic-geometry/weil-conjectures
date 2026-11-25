/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.RingTheory.CompletionOfDVR
import WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Geometric regularity of the generic fibre of a DVR completion

For a discrete valuation ring `A` whose fraction field has characteristic zero, the generic fibre
of the `𝔪_A`-adic completion `Â` is geometrically regular.

## Implementation details

Inverting a uniformizer inverts every nonzero element of the discrete valuation ring `Â`, so the
generic fibre is the field `Frac Â`; purely inseparable extensions of a characteristic-zero field
are trivial, so its base changes along them are again fields.

## References

* Stacks Project, More on Algebra, Proposition Tag 07PX.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace AdicCompletion

/-- If `A` is a discrete valuation ring whose fraction field has characteristic zero, the generic
fibre of the `𝔪_A`-adic completion of `A` is geometrically regular over `Frac A`. -/
theorem isGeometricallyRegular_genericFiber_of_isDiscreteValuationRing_of_charZero
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] :
    Algebra.IsGeometricallyRegular (⊥ : Ideal A).ResidueField
      ((⊥ : Ideal A).Fiber (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
  classical
  let B := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let k := (⊥ : Ideal A).ResidueField
  obtain ⟨hB, hDVR⟩ := AdicCompletion.isDiscreteValuationRing A
  have := hB
  have := hDVR
  have hm : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B := AdicCompletion.maximalIdeal_eq_map.symm
  have : IsFractionRing B (B ⊗[A] k) :=
    IsDiscreteValuationRing.isFractionRing_tensorProduct hm k
  let := IsFractionRing.toField B (K := B ⊗[A] k)
  let e := Algebra.TensorProduct.comm A k B
  have hf : IsField (k ⊗[A] B) := e.toRingEquiv.toMulEquiv.isField (Field.toIsField _)
  let := hf.toField
  have : CharZero A := ⟨fun m n h ↦ Nat.cast_injective (R := K) (by
    simpa only [map_natCast] using congrArg (algebraMap A K) h)⟩
  have : CharZero k := IsFractionRing.charZero_of_isFractionRing A
  refine ⟨inferInstance, ?_⟩
  intro k' _ _ _ _
  have hb := IsPurelyInseparable.bijective_algebraMap_of_isSeparable k k'
  let e' := AlgEquiv.ofBijective
    (Algebra.TensorProduct.includeRight : (k ⊗[A] B) →ₐ[k] k' ⊗[k] (k ⊗[A] B))
    (Algebra.TensorProduct.includeRight_bijective hb)
  exact IsRegularRing.of_ringEquiv e'.toRingEquiv

end AdicCompletion
