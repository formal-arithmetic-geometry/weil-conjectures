/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import WeilConjectures.RingTheory.CohenRing
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.RingTheory.MvPowerSeries.Basic
import WeilConjectures.RingTheory.FormallySmoothAdicSmallKernelCriterion
import WeilConjectures.RingTheory.PowerSeriesParameterPreservingRingLift
import WeilConjectures.RingTheory.ClosedFiberDefectDerivationExtension

/-! # Formal smoothness of parameter-preserving power-series maps

A map between field or Cohen power-series rings carrying parameters into parameters is adically
formally smooth if its closed fibre is.

## Implementation details

No arbitrary complete local rings or flat maps occur in this criterion: it is the coordinate
lifting step of Stacks Tag 07NQ.

## References

* [Stacks, Tag 07NQ] (proof of (2) implies (3), final lifting argument)
* [Stacks, Tag 07NM]
* [Stacks, Tag 07NL]
* [Stacks, Tag 07EL]
-/

@[expose] public section

universe u v

open IsLocalRing

namespace MvPowerSeries

/-- A map between field or Cohen power-series rings carrying parameters into parameters
is adically formally smooth if its closed fibre is. -/
theorem formallySmoothAdic_of_parameters_closedFiber
    (ΛR : Type u) (ΛT : Type v) [CommRing ΛR] [CommRing ΛT] (n m : ℕ)
    [IsRegularLocalRing (MvPowerSeries (Fin n) ΛR)]
    [IsRegularLocalRing (MvPowerSeries (Fin m) ΛT)]
    (i : MvPowerSeries (Fin n) ΛR →+* MvPowerSeries (Fin m) ΛT) [IsLocalHom i]
    (t : List (MvPowerSeries (Fin n) ΛR))
    (y : List (MvPowerSeries (Fin m) ΛT))
    (ht : IsRegularSystemOfParameters t)
    (hy : IsRegularSystemOfParameters (t.map i ++ y))
    (hcoeff : (IsField ΛR ∧ IsField ΛT ∧ CharZero ΛR ∧ CharZero ΛT) ∨
      ∃ p : ℕ, p.Prime ∧ IsCohenRing p ΛR ∧ IsCohenRing p ΛT ∧
        t.head? = some (p : MvPowerSeries (Fin n) ΛR)) :
    let R := MvPowerSeries (Fin n) ΛR
    let T := MvPowerSeries (Fin m) ΛT
    letI : Algebra R T := i.toAlgebra
    let L : Ideal T := (maximalIdeal R).map i
    letI : Algebra (R ⧸ maximalIdeal R) (T ⧸ L) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
        maximalIdeal R ≤ L.comap (algebraMap R T))
    Algebra.FormallySmoothAdic (R ⧸ maximalIdeal R) (T ⧸ L)
        ((maximalIdeal T).map (Ideal.Quotient.mk L)) →
      Algebra.FormallySmoothAdic R T (maximalIdeal T) := by
  dsimp only
  let R := MvPowerSeries (Fin n) ΛR
  let T := MvPowerSeries (Fin m) ΛT
  let : Algebra R T := i.toAlgebra
  intro hclosed
  apply Algebra.formallySmoothAdic_of_smallKernel_lifts R T (maximalIdeal T)
  intro D _ _ J hJ g hg hsmall
  obtain ⟨f, hf, hft⟩ := exists_parameterPreserving_ringLift ΛR ΛT n m i t y
    hy hcoeff D J hJ g hg
  obtain ⟨δ, hδone, hδmem, hδmul, hδbase⟩ :=
    Algebra.exists_closedFiber_defect_derivation R T t ht.1 hclosed
      D J hJ g f hf hft hsmall
  have hδprod (x z : T) : δ x * δ z = 0 := by
    have hmem : δ x * δ z ∈ J ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (hδmem x) (hδmem z)
    simpa only [hJ, Ideal.mem_bot] using hmem
  let l : T →ₐ[R] D :=
    { toFun := fun x ↦ f x - δ x
      map_zero' := by simp
      map_one' := by simp [hδone]
      map_add' := fun x z ↦ by simp only [map_add]; ring
      map_mul' := fun x z ↦ by
        simp only [map_mul, hδmul]
        linear_combination -(hδprod x z)
      commutes' := fun r ↦ by
        change f (algebraMap R T r) - δ (algebraMap R T r) = algebraMap R D r
        rw [hδbase]
        ring }
  refine ⟨l, ?_⟩
  ext x
  change Ideal.Quotient.mk J (f x - δ x) = g x
  rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr (hδmem x), sub_zero]
  exact RingHom.congr_fun hf x

end MvPowerSeries
