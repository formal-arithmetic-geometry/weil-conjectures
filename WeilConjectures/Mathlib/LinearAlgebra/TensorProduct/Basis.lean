/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Separating families of linear forms on a tensor product

Over a field `K`, if the linear forms in `S` separate the points of `M` and those in `T` separate
the points of `N`, then the products `f ⊗ g` with `f ∈ S` and `g ∈ T` separate the points of
`M ⊗[K] N`.

## Blueprint

- `sk-p-comparison`: the rational points of a product of reduced varieties over an algebraically
  closed field are dense.
-/

@[expose] public section

namespace TensorProduct

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- Over a field, if the linear forms in `S` separate the points of `M` and those in `T` separate
the points of `N`, then an element of `M ⊗[K] N` killed by every `f ⊗ g` with `f ∈ S` and `g ∈ T`
is zero.

Write `t = ∑ᵢ mᵢ ⊗ bᵢ` for a basis `(bᵢ)` of `N`; for `f ∈ S` the vector `∑ᵢ f(mᵢ) bᵢ` is killed by
every `g ∈ T`, so it vanishes, hence `f(mᵢ) = 0` for all `i` and `f ∈ S`, so every `mᵢ` is zero. -/
theorem eq_zero_of_forall_map_eq_zero (S : Set (Module.Dual K M)) (T : Set (Module.Dual K N))
    (hS : ∀ m, (∀ f ∈ S, f m = 0) → m = 0) (hT : ∀ n, (∀ g ∈ T, g n = 0) → n = 0)
    {t : M ⊗[K] N} (ht : ∀ f ∈ S, ∀ g ∈ T, TensorProduct.lid K K (TensorProduct.map f g t) = 0) :
    t = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace K N
  obtain ⟨c, rfl⟩ := (equivFinsuppOfBasisRight b).symm.surjective t
  suffices c = 0 by simp [this]
  ext i
  refine hS _ fun f hf ↦ ?_
  have hsum : (c.mapRange f f.map_zero).sum (fun j a ↦ a • b j) = 0 := by
    refine hT _ fun g hg ↦ ?_
    have := ht f hf g hg
    simp only [equivFinsuppOfBasisRight_symm_apply, Finsupp.sum, map_sum, map_tmul,
      lid_tmul] at this
    rw [Finsupp.sum_mapRange_index (by simp), Finsupp.sum, map_sum]
    simpa using this
  have := congr(b.repr $hsum i)
  simpa [← Finsupp.linearCombination_apply] using this

end TensorProduct
