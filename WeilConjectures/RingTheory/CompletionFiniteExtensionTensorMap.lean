/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The completed tensor map of a localized algebra

For an `R`-algebra `S` and a prime `p` of `R`, we construct the canonical `S`-algebra map
`R_p^∧ ⊗[R] S → (R_p ⊗[R] S)^∧`, where the target is the `p`-adic completion.

## Implementation details

At level `n`, the map `A ⧸ m^n → B ⧸ J^n` is `a ↦ a ⊗ 1`. These maps commute with reduction
and define `C → B^∧`; the tensor universal property extends this and the structural map
`S → B^∧` to `C ⊗[R] S`. The construction does not need finiteness.

## References

* [Stacks, Tag 07N9], first equality
-/

@[expose] public section

universe u v
open scoped TensorProduct
namespace AdicCompletion

/-- The canonical map from the completed localized base tensored with a finite algebra
into the completion of the localized algebra. -/
noncomputable def completionFiniteExtensionTensorMap
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := A ⊗[R] S
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
    let J := p.map (algebraMap R B)
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
    (C ⊗[R] S) →ₐ[S] AdicCompletion J B := by
  let A := Localization.AtPrime p
  let m := IsLocalRing.maximalIdeal A
  let C := AdicCompletion m A
  let B := A ⊗[R] S
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
  let J := p.map (algebraMap R B)
  let f : A →ₐ[R] B := Algebra.TensorProduct.includeLeft
  have hmap : m.map f.toRingHom = J := by
    rw [show m = p.map (algebraMap R A) from
      (Localization.AtPrime.map_eq_maximalIdeal (I := p)).symm, Ideal.map_map]
    congr 1
  have hpow (n : ℕ) : m ^ n ≤ (J ^ n).comap f.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_pow, hmap]
  let q (n : ℕ) : A ⧸ m ^ n →ₐ[R] B ⧸ J ^ n :=
    Ideal.quotientMapₐ (J ^ n) f (hpow n)
  let g (n : ℕ) : C →ₐ[R] B ⧸ J ^ n :=
    (q n).comp ((evalₐ m n).restrictScalars R)
  have hg {i j : ℕ} (h : i ≤ j) :
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)).comp (g j) = g i := by
    apply AlgHom.ext
    intro x
    have he : Ideal.Quotient.factorPow m h (evalₐ m j x) = evalₐ m i x := by
      apply induction_on m A x
      intro a
      simp only [evalₐ_mk]
      exact AdicCompletion.Ideal.mk_eq_mk m h a
    have hq : (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)).comp (q j) =
        (q i).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)) := by
      apply AlgHom.ext
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rfl
    change Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)
      (q j (evalₐ m j x)) = q i (evalₐ m i x)
    exact (AlgHom.congr_fun hq _).trans (congrArg (q i) he)
  let ghat : C →ₐ[R] AdicCompletion J B := liftAlgHom J g (fun h ↦ hg h)
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
  exact ((AlgHom.liftEquiv R S C (AdicCompletion J B)) ghat).comp
    (Algebra.TensorProduct.commRight R S C).symm.toAlgHom

end AdicCompletion
