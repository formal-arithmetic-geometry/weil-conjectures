/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import WeilConjectures.RingTheory.CompletionTensorQuotientSeparated
import WeilConjectures.RingTheory.LocalTensorQuotientDetection

/-!
# Injectivity of the local completion comparison

For a finite algebra `S` over a Noetherian ring `R` and a prime `p`, an `S`-algebra map
`R_p^∧ ⊗[R] S → ∏ q, S_q^∧` compatible with the local maps is injective.

## Implementation details

An element of the tensor product is detected modulo each power of the maximal ideal
(`completion_tensor_quotient_separated`). Writing it as a finite sum of pure tensors, its
images in the quotients of the `S_q` vanish, and `local_tensor_quotient_detection` shows the
corresponding quotient element of the tensor product vanishes.

## References

* [Stacks, Tag 07N9], the quotient product decomposition and the application of
  [Stacks, Tag 00MA]
* [Stacks, Tag 00JA]
* [Stacks, Tag 00CT]
* [Stacks, Tag 0394]
-/

@[expose] public section

universe u v
open scoped TensorProduct
namespace AdicCompletion

/-- Local completion maps detect equality of completed tensors: an `S`-algebra map
`R_p^∧ ⊗[R] S → ∏ q, S_q^∧` that is levelwise induced by the local maps `R_p → S_q` is
injective. -/
theorem completion_tensor_localMaps_injective
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    let C := AdicCompletion m A
    let Q := p.primesOver S
    let D := fun q : Q ↦
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
        (Localization.AtPrime q.1)
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
    ∀ (f : (C ⊗[R] S) →ₐ[S] (∀ q : Q, D q)),
      (∀ (q : Q) (n : ℕ) (a : C) (r : A),
        evalₐ m n a = Ideal.Quotient.mk (m ^ n) r →
        evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) n
            (f (a ⊗ₜ[R] (1 : S)) q) =
          Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ n)
            (Localization.localRingHom p q.1 (algebraMap R S)
              (Ideal.LiesOver.over (P := q.1) (p := p)) r)) →
      Function.Injective f := by
  classical
  dsimp only
  intro f hf
  let A := Localization.AtPrime p
  let m := IsLocalRing.maximalIdeal A
  let C := AdicCompletion m A
  let Q := p.primesOver S
  let D := fun q : Q ↦
    AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
      (Localization.AtPrime q.1)
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
  suffices hzero : ∀ x : C ⊗[R] S, f x = 0 → x = 0 by
    intro x y hxy
    have h := hzero (x - y) (by rw [map_sub, hxy, sub_self])
    exact sub_eq_zero.mp h
  intro x hx
  apply completion_tensor_quotient_separated R S p x
  intro n
  obtain ⟨k, hnk, hk⟩ := local_tensor_quotient_detection R S p n
  obtain ⟨t, ht⟩ := TensorProduct.exists_finset x
  choose r hr using fun a : C ↦ Ideal.Quotient.mk_surjective (evalₐ m k a)
  have hlocal (q : Q) :
      ∑ i ∈ t, Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ k)
        (Localization.localRingHom p q.1 (algebraMap R S)
          (Ideal.LiesOver.over (P := q.1) (p := p)) (r i.1) *
          algebraMap S (Localization.AtPrime q.1) i.2) = 0 := by
    have hqx := congrArg
      (fun z : ∀ q : Q, D q ↦
        evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) k (z q)) hx
    rw [ht, map_sum] at hqx
    simp only [Finset.sum_apply, map_sum, Pi.zero_apply, map_zero] at hqx
    have hpure (a : C) (s : S) :
        evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) k
          (f (a ⊗ₜ[R] s) q) =
        Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ k)
          (Localization.localRingHom p q.1 (algebraMap R S)
            (Ideal.LiesOver.over (P := q.1) (p := p)) (r a) *
            algebraMap S (Localization.AtPrime q.1) s) := by
      have hs : a ⊗ₜ[R] s = s • (a ⊗ₜ[R] (1 : S)) := by
        simp [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
          Algebra.TensorProduct.tmul_mul_tmul]
      rw [hs, map_smul]
      change evalₐ _ k (s • f (a ⊗ₜ[R] (1 : S)) q) = _
      rw [AlgHom.map_smul_of_tower, hf q k a (r a) (hr a).symm]
      simp [Algebra.smul_def, mul_comm]
    simpa only [hpure] using hqx
  have hz := hk (C × S) t (fun i ↦ r i.1) (fun i ↦ i.2) hlocal
  have hrepr (a : C) : evalₐ m n a = Ideal.Quotient.mk (m ^ n) (r a) := by
    have hv : a.val k = Submodule.Quotient.mk (r a) := by
      have h := factor_evalₐ_eq_eval m (n := k) a (by simp)
      rw [← hr a] at h
      exact h.symm
    have hvn := a.property hnk
    rw [hv] at hvn
    have h := factor_eval_eq_evalₐ m (n := n) a (by simp)
    rw [show eval m A n a = Submodule.Quotient.mk (r a) from hvn.symm] at h
    exact h.symm
  rw [ht, map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.restrictScalars_apply, AlgHom.id_apply]
  change (∑ i ∈ t, evalₐ m n i.1 ⊗ₜ[R] i.2) = 0
  simpa only [hrepr] using hz

end AdicCompletion
