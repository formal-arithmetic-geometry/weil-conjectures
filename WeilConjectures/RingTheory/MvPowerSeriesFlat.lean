/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Flatness of the constant inclusion into power series

For a Noetherian ring `B`, the inclusion of constants `B → B⟦x₁, …, xₙ⟧` is flat.

## Implementation details

The power-series ring is the completion of the Noetherian polynomial ring `B[x₁, …, xₙ]` at the
ideal of the variables, and Noetherian adic completion is flat (Stacks 00MB); the polynomial ring
is free over `B`.

## References

* [Stacks, Tag 0EYA] (first paragraph)
* [Stacks, Tag 00MB]
-/

@[expose] public section

universe u
namespace MvPowerSeries

/-- The inclusion of constants into a finite-variable power-series ring is flat. -/
theorem constants_flat (B : Type u) [CommRing B] [IsNoetherianRing B] (n : ℕ) :
    (C (σ := Fin n) (R := B)).Flat := by
  let P := MvPolynomial (Fin n) B
  let I := MvPolynomial.idealOfVars (Fin n) B
  let e := toAdicCompletionAlgEquiv (Fin n) B
  have hP : (algebraMap B P).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hC : (algebraMap P (AdicCompletion I P)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have hflat := hP.comp hC
  have heq : e.toRingHom.comp (C (σ := Fin n) (R := B)) =
      (algebraMap P (AdicCompletion I P)).comp (algebraMap B P) := by
    apply RingHom.ext
    intro b
    change e (C b) = _
    rw [← MvPolynomial.coe_C, toAdicCompletionAlgEquiv_apply, toAdicCompletion_coe]
    rfl
  apply (RingHom.Flat.comp_iff_of_bijective_left
    (f := C (σ := Fin n) (R := B)) (g := e.toRingHom) e.bijective).mp
  rwa [heq]

end MvPowerSeries
