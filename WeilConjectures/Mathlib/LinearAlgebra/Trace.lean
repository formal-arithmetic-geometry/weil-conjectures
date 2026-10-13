/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Trace

/-!
# The trace of conjugation on a space of linear maps

For endomorphisms `g` of `N` and `h` of `M` (free of finite rank), the endomorphism
`f ↦ g ∘ f ∘ h` of `M →ₗ N` has trace `tr(g) tr(h)`
(`LinearMap.trace_compLeft_compRight`). Consequently, if a perfect pairing `V × M → N`
intertwines endomorphisms `F_V`, an automorphism `F_M` and `F_N`, then
`tr(F_V) = tr(F_N) tr(F_M⁻¹)` (`LinearMap.trace_eq_mul_of_bijective`).
-/

@[expose] public section

open TensorProduct

namespace LinearMap

variable {R M N V : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M] [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
  [AddCommGroup V] [Module R V]

/-- The trace of the endomorphism `f ↦ g ∘ f ∘ h` of `M →ₗ N` is `tr(g) tr(h)`: under the
identification `M^∨ ⊗ N ≅ (M →ₗ N)` it is `hᵀ ⊗ g`. -/
theorem trace_compLeft_compRight (g : N →ₗ[R] N) (h : M →ₗ[R] M) :
    trace R (M →ₗ[R] N) ((llcomp R M N N g) ∘ₗ (llcomp R M M N).flip h) =
      trace R N g * trace R M h := by
  have h₁ : (dualTensorHomEquiv R M N).toLinearMap ∘ₗ map (Module.Dual.transpose (R := R) h) g =
      ((llcomp R M N N g) ∘ₗ (llcomp R M M N).flip h) ∘ₗ
        (dualTensorHomEquiv R M N).toLinearMap := by
    refine TensorProduct.ext' fun f n ↦ LinearMap.ext fun m ↦ ?_
    simp [Module.Dual.transpose_apply, dualTensorHom_apply]
  have hc : (dualTensorHomEquiv R M N).conj (map (Module.Dual.transpose (R := R) h) g) =
      (llcomp R M N N g) ∘ₗ (llcomp R M M N).flip h := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨y, rfl⟩ := (dualTensorHomEquiv R M N).surjective x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun h₁ y
  rw [← hc, trace_conj', trace_tensorProduct', trace_transpose', mul_comm]

/-- If a perfect pairing `p : V × M → N` intertwines endomorphisms `F_V` of `V` and `F_N` of `N`
with an automorphism `F_M` of `M`, `p (F_V v) (F_M m) = F_N (p v m)`, then
`tr(F_V) = tr(F_N) tr(F_M⁻¹)`: under `V ≅ (M →ₗ N)`, `F_V` is `f ↦ F_N ∘ f ∘ F_M⁻¹`. -/
theorem trace_eq_mul_of_bijective (p : V →ₗ[R] M →ₗ[R] N) (hp : Function.Bijective p)
    (fV : V →ₗ[R] V) (fM : M ≃ₗ[R] M) (fN : N →ₗ[R] N)
    (h : ∀ v m, p (fV v) (fM m) = fN (p v m)) :
    trace R V fV = trace R N fN * trace R M fM.symm.toLinearMap := by
  let e := LinearEquiv.ofBijective p hp
  have hc : e.conj fV = (llcomp R M N N fN) ∘ₗ (llcomp R M M N).flip fM.symm.toLinearMap := by
    refine LinearMap.ext fun f ↦ LinearMap.ext fun m ↦ ?_
    obtain ⟨v, rfl⟩ := e.surjective f
    have := h v (fM.symm m)
    simp only [LinearEquiv.apply_symm_apply] at this
    simp [LinearEquiv.conj_apply, e, this]
  rw [← trace_compLeft_compRight, ← hc, trace_conj']

/-- The trace of the operator `φ ↦ g ∘ φ ∘ h` on `M →ₗ[R] N` is `tr g * tr h`. -/
theorem trace_llcomp_comp_lcomp (g : N →ₗ[R] N) (h : M →ₗ[R] M) :
    trace R (M →ₗ[R] N) (llcomp R M N N g ∘ₗ lcomp R N h) = trace R N g * trace R M h :=
  trace_compLeft_compRight g h

end LinearMap
