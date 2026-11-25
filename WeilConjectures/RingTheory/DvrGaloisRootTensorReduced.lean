/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Unramified.Field

/-! # Reducedness of generic tensor algebras for a DVR root extension

For a uniformizer `π` of a discrete valuation ring `B`, `n ≥ 1`, and a finite Galois extension `E`
of `Frac B`, the algebra `E ⊗_B B[t]/(t^n - π)` is reduced.

## Implementation details

`t^n - π` is Eisenstein, so `A = B[t]/(t^n - π)` is a domain; by flatness `E ⊗_B A` embeds in
`E ⊗_{Frac B} Frac A`, which is reduced since `E` is finite separable over `Frac B`. Neither
invertibility of `n` nor separability of `Frac A / Frac B` is needed.

## References

* Stacks Project, Tag 09EV.
-/

@[expose] public section

universe u
open scoped TensorProduct
namespace RingTheory

/-- The generic tensor algebra of a positive-degree uniformizer root is reduced: if `π` is a
uniformizer of the discrete valuation ring `B`, `n ≥ 1`, and `E` is a finite Galois extension of
`Frac B`, then `E ⊗_B B[t]/(t^n - π)` is reduced. -/
theorem dvr_galois_root_tensor_reduced
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi) (n : ℕ) (hnpos : 0 < n)
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    (hE : FiniteDimensional (FractionRing B) E ∧ IsGalois (FractionRing B) E) :
    let : Algebra B E :=
      ((algebraMap (FractionRing B) E).comp
        (algebraMap B (FractionRing B))).toAlgebra
    IsReduced (E ⊗[B]
      AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)) := by
  let : Algebra B E :=
    ((algebraMap (FractionRing B) E).comp
      (algebraMap B (FractionRing B))).toAlgebra
  let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
  have hmon := Polynomial.monic_X_pow_sub_C pi (Nat.ne_of_gt hnpos)
  have heis : ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi).IsEisensteinAt
      (Ideal.span {pi}) := by
    refine hmon.isEisensteinAt_of_mem_of_notMem ?_ ?_ ?_
    · exact (Ideal.span_singleton_eq_top).not.mpr hpi.not_isUnit
    · intro k hk
      rw [Polynomial.natDegree_X_pow_sub_C] at hk
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
        ite_eq_right (Nat.ne_of_lt hk), zero_sub]
      by_cases hk0 : k = 0
      · subst k
        simp [Polynomial.coeff_C]
      · simp [Polynomial.coeff_C, hk0]
    · simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
        ite_eq_right (Nat.ne_of_gt hnpos).symm, Polynomial.coeff_C_zero, zero_sub,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton, dvd_neg]
      simpa only [pow_one] using
        (pow_dvd_pow_iff hpi.ne_zero hpi.not_isUnit).not.mpr (by omega : ¬ 2 ≤ 1)
  have hprime : (Ideal.span {pi}).IsPrime :=
    (Ideal.span_singleton_prime hpi.ne_zero).mpr (irreducible_iff_prime.mp hpi)
  have hirr := heis.irreducible hprime hmon.isPrimitive
    (by simpa only [Polynomial.natDegree_X_pow_sub_C] using hnpos)
  have : IsDomain A := AdjoinRoot.isDomain_of_prime (irreducible_iff_prime.mp hirr)
  have hBA : Function.Injective (algebraMap B A) :=
    AdjoinRoot.of.injective_of_degree_ne_zero
      (by rw [Polynomial.degree_X_pow_sub_C hnpos];
          exact_mod_cast (Nat.ne_of_gt hnpos))
  have : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hBA
  have : FaithfulSMul B (FractionRing A) :=
    (faithfulSMul_iff_algebraMap_injective B (FractionRing A)).mpr
      ((IsFractionRing.injective A (FractionRing A)).comp hBA)
  let : Algebra (FractionRing B) (FractionRing A) := FractionRing.liftAlgebra B _
  have : IsScalarTower B (FractionRing B) (FractionRing A) :=
    FractionRing.isScalarTower_liftAlgebra B _
  have : IsScalarTower B (FractionRing B) E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Flat B E := Module.Flat.trans B (FractionRing B) E
  let g : A →ₐ[B] FractionRing A := IsScalarTower.toAlgHom B A (FractionRing A)
  let f : E ⊗[B] A →ₐ[B] E ⊗[B] FractionRing A :=
    Algebra.TensorProduct.map (AlgHom.id B E) g
  have hf : Function.Injective f := by
    change Function.Injective
      (_root_.TensorProduct.map (LinearMap.id : E →ₗ[B] E) g.toLinearMap)
    exact Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap
      (IsFractionRing.injective A (FractionRing A))
  let e := IsLocalization.algebraTensorEquiv (nonZeroDivisors B) (FractionRing B)
    E (FractionRing A)
  have : FiniteDimensional (FractionRing B) E := hE.1
  have : IsGalois (FractionRing B) E := hE.2
  have : Algebra.FormallyUnramified (FractionRing B) E :=
    Algebra.FormallyUnramified.of_isSeparable _ _
  have : Algebra.FormallyUnramified (FractionRing A) (FractionRing A ⊗[FractionRing B] E) :=
    inferInstance
  have : IsReduced (FractionRing A ⊗[FractionRing B] E) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing A) _
  exact isReduced_of_injective
    (((Algebra.TensorProduct.comm (FractionRing B) E (FractionRing A)).toRingHom).comp
      (e.symm.toRingHom.comp f.toRingHom))
    ((Algebra.TensorProduct.comm (FractionRing B) E (FractionRing A)).injective.comp
      (e.symm.injective.comp hf))

end RingTheory
