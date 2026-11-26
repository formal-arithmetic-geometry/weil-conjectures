/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.PurelyInseparableIntegralPrimeUnique
import WeilConjectures.RingTheory.CompletionFiniteExtension
import WeilConjectures.RingTheory.Derivation.CompletionAndLocalization
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.RingTheory.Derivation.Localization

/-! # Extending finite-model derivations to a generic formal fibre

Let `A` be a Noetherian normal domain with fraction field `K`, `q` a prime of `A`, `M` a finite
purely inseparable extension of `K` and `B ⊆ M` a finite `A`-subalgebra with fraction field `M`.
Every absolute derivation of `B` extends to `M ⊗_K (formal fibre of A at q)`.

## Implementation details

Pure inseparability and normality of `A` give a unique prime `r` of `B` over `q`, so the
completion of `A_q` tensored with `B` is the completion of `B_r`. The formal fibre is then
identified with `completion(B_r) ⊗_B M`, a localization of `completion(B_r)`. The derivation is
extended to `B_r` by the quotient rule, to its completion, and once more by the quotient rule,
and finally transported along the ring equivalences. No nontriviality hypothesis is needed.

## References

* [Stacks, Tag 07PR]
* [Stacks, Tag 07PE]
* [Stacks, Tag 07N9]
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace Derivation

private theorem transport {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (D : Derivation ℤ R R) :
    ∃ E : Derivation ℤ S S, ∀ x : R, E (e x) = e (D x) := by
  let d : S →+ S := e.toAddMonoidHom.comp
    (D.toLinearMap.toAddMonoidHom.comp e.symm.toAddMonoidHom)
  let E : Derivation ℤ S S :=
    { toFun := d
      map_add' := d.map_add
      map_smul' := by
        intro z x
        simpa only [Algebra.smul_def, Int.cast_smul_eq_zsmul, RingHom.id_apply]
          using d.map_zsmul z x
      map_one_eq_zero' := by simp [d]
      leibniz' := by
        intro x y
        change e (D (e.symm (x * y))) =
          x * e (D (e.symm y)) + y * e (D (e.symm x))
        rw [map_mul, D.leibniz]
        simp only [smul_eq_mul, map_add, map_mul, e.apply_symm_apply] }
  exact ⟨E, by intro x; simp [E, d]⟩

private theorem localize {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (W : Submonoid R) [IsLocalization W S] (D : Derivation ℤ R R) :
    ∃ E : Derivation ℤ S S, ∀ x : R,
      E (algebraMap R S x) = algebraMap R S (D x) := by
  let ψ : S →+* S := RingHom.id _
  let δ : R →+ S := (algebraMap R S).toAddMonoidHom.comp
    D.toLinearMap.toAddMonoidHom
  have hδ : ∀ x y, δ (x * y) = ψ (algebraMap R S x) • δ y +
      ψ (algebraMap R S y) • δ x := by
    intro x y
    change algebraMap R S (D (x * y)) =
      algebraMap R S x * algebraMap R S (D y) +
        algebraMap R S y * algebraMap R S (D x)
    rw [D.leibniz]
    simp only [smul_eq_mul, map_add, map_mul]
  let d := IsLocalization.extendDerivation W ψ δ hδ
  let E : Derivation ℤ S S :=
    { toFun := d
      map_add' := d.map_add
      map_smul' := by
        intro z x
        simpa only [Algebra.smul_def, Int.cast_smul_eq_zsmul, RingHom.id_apply]
          using d.map_zsmul z x
      map_one_eq_zero' := by
        have h := IsLocalization.extendDerivation_mul W ψ δ hδ 1 1
        simp only [ψ, RingHom.id_apply, one_smul, one_mul] at h
        exact add_eq_left.mp h.symm
      leibniz' := IsLocalization.extendDerivation_mul W ψ δ hδ }
  exact ⟨E, fun x ↦ IsLocalization.extendDerivation_algebraMap W ψ δ hδ x⟩

private theorem extend_from_tensor
    {B H M R : Type*} [CommRing B] [CommRing H] [Field M] [CommRing R]
    [Algebra B H] [Algebra B M] [IsFractionRing B M] [Algebra M R]
    (D : Derivation ℤ B B) (Dh : Derivation ℤ H H)
    (hDh : ∀ b, Dh (algebraMap B H b) = algebraMap B H (D b))
    (e : R ≃ₐ[M] (M ⊗[B] H)) :
    ∃ E : Derivation ℤ R R, ∀ b : B,
      E (algebraMap M R (algebraMap B M b)) =
        algebraMap M R (algebraMap B M (D b)) := by
  let T := M ⊗[B] H
  let : Algebra H T := Algebra.TensorProduct.rightAlgebra
  let : IsLocalization (Algebra.algebraMapSubmonoid H (nonZeroDivisors B)) T :=
    IsLocalization.tensorRight (S := H) M (nonZeroDivisors B)
  obtain ⟨Dt, hDt⟩ := localize
    (Algebra.algebraMapSubmonoid H (nonZeroDivisors B)) Dh (S := T)
  obtain ⟨E, hE⟩ := transport e.symm.toRingEquiv Dt
  change ∀ x : T, E (e.symm x) = e.symm (Dt x) at hE
  have hb (b : B) : e (algebraMap M R (algebraMap B M b)) =
      algebraMap H T (algebraMap B H b) := by
    rw [e.commutes]
    change (algebraMap B M b) ⊗ₜ[B] (1 : H) =
      (1 : M) ⊗ₜ[B] (algebraMap B H b)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    exact TensorProduct.smul_tmul b (1 : M) (1 : H)
  refine ⟨E, fun b ↦ ?_⟩
  rw [← e.symm_apply_apply (algebraMap M R (algebraMap B M b)), hE, hb, hDt, hDh,
    ← hb (D b)]
  exact e.symm_apply_apply _

/-- Every absolute derivation of a finite integral model extends to the base-changed
formal fibre, compatibly with the model's inclusion into its fraction field. -/
theorem exists_formalFiber_extension
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime]
    (M : Type v) [Field M] [Algebra (⊥ : Ideal A).ResidueField M]
    [Algebra A M] [IsScalarTower A (⊥ : Ideal A).ResidueField M]
    [Module.Finite (⊥ : Ideal A).ResidueField M]
    [IsPurelyInseparable (⊥ : Ideal A).ResidueField M]
    (B : Subalgebra A M) [Module.Finite A B] [IsFractionRing B M]
    (D : Derivation ℤ B B) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    let R := TensorProduct (⊥ : Ideal A).ResidueField M ((⊥ : Ideal A).Fiber C)
    ∃ E : Derivation ℤ R R, ∀ b : B,
      E (Algebra.TensorProduct.includeLeftRingHom (b : M)) =
        Algebra.TensorProduct.includeLeftRingHom (D b : M) := by
  classical
  let K := (⊥ : Ideal A).ResidueField
  let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (Localization.AtPrime q)
  let R := TensorProduct K M ((⊥ : Ideal A).Fiber C)
  obtain ⟨r, hr, huniq⟩ := purelyInseparable_integral_prime_unique A B
    (inferInstance : IsIntegrallyClosed A) K M q
  let : r.IsPrime := hr.1
  let : r.LiesOver q := ⟨hr.2.symm⟩
  let Q := q.primesOver B
  let rQ : Q := Ideal.primesOver.mk q r
  let : Unique Q :=
    { default := rQ
      uniq := by
        intro t
        apply Subtype.ext
        exact huniq t.1 ⟨inferInstance, (Ideal.LiesOver.over (P := t.1) (p := q)).symm⟩ }
  let H := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime r))
    (Localization.AtPrime r)
  let : Algebra B H := inferInstance
  let : Module B H := Algebra.toModule
  let : DistribMulAction B H := (inferInstance : Module B H).toDistribMulAction
  let : Algebra B (C ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  obtain ⟨_, e, _, _, _, _⟩ := AdicCompletion.completion_finite_extension A B q
  let e0 : (B ⊗[A] C) ≃ₐ[B] H :=
    (Algebra.TensorProduct.commRight A B C).trans
      (e.trans (AlgEquiv.ofRingEquiv (f := RingEquiv.piUnique _) (by intro x; rfl)))
  let eR : R ≃ₐ[M] (M ⊗[B] H) :=
    (Algebra.TensorProduct.cancelBaseChange A K M M C).trans
      ((Algebra.TensorProduct.cancelBaseChange A B M M C).symm.trans
        (Algebra.TensorProduct.congr (AlgEquiv.refl : M ≃ₐ[M] M) e0))
  obtain ⟨Dr, hDr⟩ := localize r.primeCompl D
    (S := Localization.AtPrime r)
  obtain ⟨Dh, _, hDh, _, _⟩ :=
    (exists_completion_and_unique_localization (Localization.AtPrime r) Dr).1
      (IsLocalRing.maximalIdeal (Localization.AtPrime r))
  apply extend_from_tensor D Dh _ eR
  intro b
  change Dh (algebraMap (Localization.AtPrime r) H
    (algebraMap B (Localization.AtPrime r) b)) = _
  rw [hDh, hDr]
  rfl

end Derivation
