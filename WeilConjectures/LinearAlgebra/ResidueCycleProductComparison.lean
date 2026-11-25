/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
/-!
# Extension of residue cycle comparisons to product terms

Additive comparison maps defined on subspaces `Z i` of `κ ⊗ M i` extend to a single additive map
on `κ ⊗ ∏ i, M i` along the tensorized coordinate projections.

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
-/
@[expose] public section
set_option autoImplicit false
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
/-- Extend cycle comparison homomorphisms along tensorized coordinate projections.
If each `β i : Z i →+ H i` sends the base change of `b i φ` to `c i` for admissible `φ`, then
there is `γ : κ ⊗ (∀ i, M i) →+ ∀ i, H i` sending the base change of `LinearMap.pi (b · (φ ·))`
at `z` to `fun i ↦ c i z`. -/
theorem residue_cycle_product_comparison
    {R κ : Type*} [CommRing R] [Field κ] [Algebra R κ]
    {ι : Type*} {V : Type*} [AddCommGroup V] [Module R V]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    {H : ι → Type*} [∀ i, AddCommGroup (H i)]
    {P : ι → Type*}
    (Z : ∀ i, Submodule κ (κ ⊗[R] M i)) (β : ∀ i, Z i →+ H i)
    (b : ∀ i, P i → V →ₗ[R] M i) (h : ∀ i, P i → Prop)
    (c : ∀ i, (κ ⊗[R] V) → H i)
    (hc : ∀ i φ, h i φ → ∀ z, ∃ hz : (b i φ).baseChange κ z ∈ Z i,
      β i ⟨(b i φ).baseChange κ z, hz⟩ = c i z) :
    ∃ γ : (κ ⊗[R] (∀ i, M i)) →+ (∀ i, H i),
      ∀ (φ : ∀ i, P i), (∀ i, h i (φ i)) → ∀ z,
        γ ((LinearMap.pi (fun i ↦ b i (φ i))).baseChange κ z) = fun i ↦ c i z := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : ∀ i, Submodule κ (κ ⊗[R] M i),
      ∀ i, IsCompl (Z i) (T i) :=
    Classical.axiom_of_choice (fun i ↦ (Z i).exists_isCompl)
  let π := fun i ↦ (LinearMap.proj i : (∀ i, M i) →ₗ[R] M i)
  let γ : (κ ⊗[R] (∀ i, M i)) →+ (∀ i, H i) :=
    AddMonoidHom.pi (fun i ↦ (β i).comp
      (((Z i).projectionOnto (T i) (hT i)).toAddMonoidHom.comp
        ((π i).baseChange κ).toAddMonoidHom))
  refine ⟨γ, ?_⟩
  intro φ hφ z
  funext i
  obtain ⟨hz, heq⟩ := hc i (φ i) (hφ i) z
  let t := LinearMap.pi (fun i ↦ b i (φ i))
  have hcoord : (π i).baseChange κ (t.baseChange κ z) = (b i (φ i)).baseChange κ z := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    rfl
  have hproj : (Z i).projectionOnto (T i) (hT i)
      ((π i).baseChange κ (t.baseChange κ z)) = ⟨(b i (φ i)).baseChange κ z, hz⟩ := by
    rw [hcoord]
    exact Submodule.projectionOnto_apply_of_mem_left (hT i) hz
  exact (congrArg (β i) hproj).trans heq
end AlgebraicGeometry.Scheme
