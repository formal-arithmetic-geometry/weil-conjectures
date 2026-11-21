/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Invariants of a tensor product with a field extension

Source: Stacks Project, Varieties, proof of Lemma 038B,
computation of the invariant polynomial coefficients.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace TensorProduct

/-- Extension by `a ↦ a ⊗ 1` embeds a vector space as the invariants of the action on
its second tensor factor, when the automorphism group's fixed field is the base field.
Source: Stacks Project, Varieties, proof of Lemma 038B. -/
theorem injective_and_range_eq_invariants
    {k : Type u} {M : Type v} [Field k] [Field M] [Algebra k M]
    (G : Subgroup (M ≃ₐ[k] M))
    (hfixed : {y : M | ∀ τ : G, (τ : M ≃ₐ[k] M) y = y} =
      Set.range (algebraMap k M))
    (A : Type w) [AddCommGroup A] [Module k A] :
    Function.Injective ((TensorProduct.mk k A M).flip (1 : M)) ∧
      Set.range ((TensorProduct.mk k A M).flip (1 : M)) =
        {z : A ⊗[k] M | ∀ τ : G,
          LinearMap.lTensor A (τ : M ≃ₐ[k] M).toLinearEquiv.toLinearMap z = z} := by
  classical
  let b := Module.Basis.ofVectorSpace k A
  let E := equivFinsuppOfBasisLeft (N := M) b
  have coord_tmul (a : A) (y : M) (i : Module.Basis.ofVectorSpaceIndex k A) :
      E (a ⊗ₜ[k] y) i = b.repr a i • y := by
    exact equivFinsuppOfBasisLeft_apply_tmul_apply b a y i
  have coord_action (τ : G) (z : A ⊗[k] M)
      (i : Module.Basis.ofVectorSpaceIndex k A) :
      E (LinearMap.lTensor A (τ : M ≃ₐ[k] M).toLinearEquiv.toLinearMap z) i =
        (τ : M ≃ₐ[k] M) (E z i) := by
    induction z using TensorProduct.inductionOn with
    | tmul a y => simp [coord_tmul]
    | add x y hx hy => simp [hx, hy]
  constructor
  · intro a a' h
    apply b.repr.injective
    ext i
    apply (algebraMap k M).injective
    have h' := congrArg (fun z ↦ E z i) h
    simpa [coord_tmul, _root_.Algebra.smul_def] using h'
  · ext z
    constructor
    · rintro ⟨a, rfl⟩ τ
      simp
    · intro hz
      have hc : ∀ i, ∃ c : k, algebraMap k M c = E z i := by
        intro i
        apply Set.mem_range.mp
        rw [← hfixed]
        intro τ
        rw [← coord_action τ z i, hz τ]
      choose c hc using hc
      let f : Module.Basis.ofVectorSpaceIndex k A →₀ k :=
        Finsupp.onFinset (E z).support c (by
          intro i hi
          apply Finsupp.mem_support_iff.mpr
          intro hzero
          apply hi
          apply (algebraMap k M).injective
          simpa [hc i] using hzero)
      refine ⟨b.repr.symm f, E.injective ?_⟩
      ext i
      simp only [LinearMap.flip_apply, TensorProduct.mk_apply, coord_tmul,
        LinearEquiv.apply_symm_apply]
      change c i • (1 : M) = E z i
      rw [_root_.Algebra.smul_def, mul_one]
      exact hc i

end TensorProduct

namespace Algebra.TensorProduct

/-- For a `k`-algebra, the same invariant set is the image subalgebra `A ⊗ 1`, canonically
isomorphic to `A` by `a ↦ a ⊗ 1`.
Source: Stacks Project, Varieties, proof of Lemma 038B. -/
theorem range_eq_invariants_and_equiv
    {k : Type u} {M : Type v} [Field k] [Field M] [Algebra k M]
    (G : Subgroup (M ≃ₐ[k] M))
    (hfixed : {y : M | ∀ τ : G, (τ : M ≃ₐ[k] M) y = y} =
      Set.range (algebraMap k M))
    (A : Type w) [Ring A] [Algebra k A] :
    (↑(Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] M).range : Set (A ⊗[k] M)) =
        {z : A ⊗[k] M | ∀ τ : G,
          LinearMap.lTensor A (τ : M ≃ₐ[k] M).toLinearEquiv.toLinearMap z = z} ∧
      ∃ e : A ≃ₐ[k] (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] M).range,
        ∀ a : A, (e a : A ⊗[k] M) = a ⊗ₜ[k] (1 : M) := by
  obtain ⟨hinj, hrange⟩ :=
    TensorProduct.injective_and_range_eq_invariants G hfixed A
  constructor
  · exact hrange
  · refine ⟨AlgEquiv.ofInjective Algebra.TensorProduct.includeLeft hinj, ?_⟩
    intro a
    rfl


end Algebra.TensorProduct
