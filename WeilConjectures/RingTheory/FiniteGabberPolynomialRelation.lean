/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.RingTheory.FiniteGabberUpstairsRelation

/-!
# Gabber's relation after a faithfully flat base change

For a finite algebra `B` over `A` with `I` in the Jacobson radical, and `b ∈ B` lifting `(1, 0)`
in a decomposition `B / IB ≅ B₁ × B₂`, the class of `(b - 1) b ^ d` vanishes in `C ⊗[A] (B / N)`
for a faithfully flat `A`-algebra `C`, where `N` is spanned by the `i b ^ j` with `i ∈ I` and
`j ≤ d`.

## Implementation details

`C` is an étale `A`-algebra over which the idempotent `(1, 0)` lifts, localized at an element
`g ∈ 1 + IA'` given by Nakayama; it is faithfully flat since `C / IC ≅ A / I` and every maximal
ideal contains `I`. The descent of the relation to `B` is proved in an importing module.

## References

* [Stacks, Tag 0EM0]
* [Stacks, Tag 07M4]
* [Stacks, Tag 00DV]
* [Stacks, Tag 00H5]
* [Stacks, Tag 00HP]
-/

@[expose] public section

universe u v w z

open scoped BigOperators

namespace Algebra

/-- Gabber's relation vanishes after a faithfully flat base change, in the quotient
by the finite coefficient submodule. -/
theorem exists_gabber_relation_after_base_change
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (B₁ : Type w) (B₂ : Type z) [CommRing B₁] [CommRing B₂]
    [Algebra (A ⧸ I) B₁] [Algebra (A ⧸ I) B₂]
    (e : (B ⧸ I.map (algebraMap A B)) ≃+* (B₁ × B₂))
    (he : ∀ a : A, e (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B a)) =
      (algebraMap (A ⧸ I) B₁ (Ideal.Quotient.mk I a),
        algebraMap (A ⧸ I) B₂ (Ideal.Quotient.mk I a)))
    (h₁ : Function.Surjective (algebraMap (A ⧸ I) B₁))
    (b : B) (hb : e (Ideal.Quotient.mk (I.map (algebraMap A B)) b) = (1, 0)) :
    ∃ (C : CommRingCat.{u}) (f : A →+* C),
      letI : Algebra A C := f.toAlgebra;
      Module.FaithfullyFlat A C ∧ ∃ d : ℕ, 1 ≤ d ∧
        let L : (Fin (d + 1) → I) →ₗ[A] B :=
          ∑ j : Fin (d + 1), (I.subtype.comp (LinearMap.proj j)).smulRight (b ^ (j : ℕ));
        TensorProduct.mk A C (B ⧸ LinearMap.range L) 1
          ((LinearMap.range L).mkQ ((b - 1) * b ^ d)) = 0 := by
  classical
  obtain ⟨C, f, hC, d, hd, c, hc⟩ :=
    exists_gabber_upstairs_tensor_relation I hI B₁ B₂ e he h₁ b hb
  let : Algebra A C := f.toAlgebra
  refine ⟨C, f, hC, d, hd, ?_⟩
  let L : (Fin (d + 1) → I) →ₗ[A] B :=
    ∑ j : Fin (d + 1), (I.subtype.comp (LinearMap.proj j)).smulRight (b ^ (j : ℕ))
  let q := (LinearMap.range L).mkQ
  change q.lTensor C (TensorProduct.tmul A (1 : C) ((b - 1) * b ^ d)) = 0
  rw [hc, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hq : q.comp (I.subtype.smulRight (b ^ (j : ℕ))) = 0 := by
    ext i
    change Submodule.Quotient.mk _ = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    refine ⟨Pi.single j i, ?_⟩
    simp only [L, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      simp [hkj]
    · simp
  rw [← LinearMap.lTensor_comp_apply, hq, LinearMap.lTensor_zero]
  rfl

end Algebra
