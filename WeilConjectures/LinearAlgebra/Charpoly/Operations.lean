/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Multiset.Powerset
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Spectra of the operations

Over an algebraically closed field the eigenvalue multiset of an endomorphism `f`, counted with
multiplicity, is the multiset of roots `f.charpoly.roots` of its characteristic polynomial. This
file records how that multiset behaves under the standard linear-algebra operations: if `f` has
eigenvalues `α₁, …, α_r` and `g` has eigenvalues `β₁, …, β_t`, then `f ⊗ g` has eigenvalues
`α_i β_j`, the `s`-th exterior power `⋀^s f` has eigenvalues `α_{i₁} ⋯ α_{i_s}` for `i₁ < ⋯ < i_s`,
and the contragredient `f^∨` of an invertible `f` has eigenvalues `α_i⁻¹`.

## Main declarations

* `LinearMap.charpoly_roots_tensorProduct`: the eigenvalues of a tensor product of endomorphisms
  are the pairwise products of the eigenvalues of the factors.
* `LinearMap.charpoly_roots_exteriorPower`: the eigenvalues of the `s`-th exterior power of an
  endomorphism are the products over the `s`-element sub-multisets of its eigenvalues.
* `LinearMap.charpoly_roots_dualMap_inv`: the eigenvalues of the contragredient of an invertible
  endomorphism are the inverses of its eigenvalues.
-/

@[expose] public section

open scoped TensorProduct

namespace LinearMap

variable {K V W : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Blueprint `sk-p-linear-spectra`: Spectra of the operations. The eigenvalues of the tensor
product of two endomorphisms are the pairwise products of their eigenvalues, with multiplicity. -/
theorem charpoly_roots_tensorProduct (f : V →ₗ[K] V) (g : W →ₗ[K] W) :
    (TensorProduct.map f g).charpoly.roots =
      (f.charpoly.roots ×ˢ g.charpoly.roots).map fun p => p.1 * p.2 := by
  sorry

/-- Blueprint `sk-p-linear-spectra`: Spectra of the operations. The eigenvalues of the `s`-th
exterior power of an endomorphism are the products of the `s`-element sub-multisets of its
eigenvalues. -/
theorem charpoly_roots_exteriorPower (s : ℕ) (f : V →ₗ[K] V) :
    (exteriorPower.map s f).charpoly.roots =
      (f.charpoly.roots.powersetCard s).map Multiset.prod := by
  sorry

/-- Blueprint `sk-p-linear-spectra`: Spectra of the operations. The eigenvalues of the
contragredient of an invertible endomorphism, that is the dual of its inverse, are the inverses of
its eigenvalues. -/
theorem charpoly_roots_dualMap_inv (f : V ≃ₗ[K] V) :
    (f.symm : V →ₗ[K] V).dualMap.charpoly.roots =
      (f : V →ₗ[K] V).charpoly.roots.map fun a => a⁻¹ := by
  sorry

end LinearMap
