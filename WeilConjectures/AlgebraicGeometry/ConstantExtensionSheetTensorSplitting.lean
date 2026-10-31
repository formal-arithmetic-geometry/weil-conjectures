/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantExtensionSheetHeartData
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Evaluation splitting of the constant-field tensor product

Source: Deligne, Weil II, paragraph after (1.1.10), p. 152.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open scoped TensorProduct
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)

/-- The evaluation tensor splitting for the actual degree-m constant field.
Source: Deligne, Weil II, paragraph after (1.1.10), p. 152; Stacks Project, Tag 03SF.
(blueprint: lem-zl-constant-extension-sheet-tensor-splitting).

Proof: independence of distinct field embeddings implies that their evaluation vectors
span the product. The tensor evaluation map is therefore surjective. Both vector spaces
over the closure have dimension [k_m:k_0], because the extension is separable and the
closure is algebraically closed. Equal finite dimensions make evaluation injective.
The finite field cardinalities q^[k_m:k_0] = q^m give degree m. Swapping tensor factors
gives precisely t tensor b mapping to sigma(t)b, with m embeddings. -/
theorem constantExtensionSheetTensorSplitting : ZlSheetTensorSplitting D m hm := by
  classical
  let := (D.extensionEmbedding m hm).toAlgebra
  let K := D.extensionSubfield m hm
  have : Finite K := (constantExtensionField_properties D m hm).1
  let := Fintype.ofFinite D.k₀
  let := Fintype.ofFinite K
  have hdegree : Module.finrank D.k₀ K = m := by
    apply Nat.pow_right_injective (Fintype.one_lt_card (α := D.k₀))
    calc
      Fintype.card D.k₀ ^ Module.finrank D.k₀ K = Fintype.card K :=
        Module.card_eq_pow_finrank.symm
      _ = Fintype.card D.k₀ ^ m := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, D.card_base]
        exact (constantExtensionField_properties D m hm).2.1
  let f : (D.k ⊗[D.k₀] K) →ₐ[D.k] ((K →ₐ[D.k₀] D.k) → D.k) :=
    AlgHom.pi fun σ ↦ Algebra.TensorProduct.lift
      (AlgHom.id D.k D.k) σ (fun _ _ ↦ Commute.all _ _)
  have hf (b : D.k) (t : K) (σ : K →ₐ[D.k₀] D.k) :
      f (b ⊗ₜ[D.k₀] t) σ = b * σ t := rfl
  have hli : LinearIndependent D.k (fun σ : K →ₐ[D.k₀] D.k ↦ (σ : K → D.k)) := by
    exact (linearIndependent_monoidHom K D.k).comp
      (fun σ : K →ₐ[D.k₀] D.k ↦ σ.toRingHom.toMonoidHom)
      (fun _ _ h ↦ AlgHom.ext fun x ↦ DFunLike.congr_fun h x)
  have hspan : Submodule.span D.k (Set.range (fun t : K ↦
      fun σ : K →ₐ[D.k₀] D.k ↦ σ t)) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hli
  have hsurj : Function.Surjective f := by
    apply (LinearMap.range_eq_top (f := f.toLinearMap)).mp
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact ⟨1 ⊗ₜ[D.k₀] t, by ext σ; simp [hf]⟩
  have hdim : Module.finrank D.k (D.k ⊗[D.k₀] K) =
      Module.finrank D.k ((K →ₐ[D.k₀] D.k) → D.k) := by
    rw [Module.finrank_baseChange, Module.finrank_pi]
    simp [AlgHom.card D.k₀ K D.k]
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hdim).mpr hsurj
  let e := (Algebra.TensorProduct.comm D.k₀ K D.k).toRingEquiv.trans
    (AlgEquiv.ofBijective f ⟨hinj, hsurj⟩).toRingEquiv
  refine ⟨e, ?_, ?_⟩
  · intro t b σ
    exact mul_comm b (σ t)
  · change Nat.card (K →ₐ[D.k₀] D.k) = m
    rw [Nat.card_eq_fintype_card, AlgHom.card D.k₀ K D.k, hdegree]

end WeilConjectures
