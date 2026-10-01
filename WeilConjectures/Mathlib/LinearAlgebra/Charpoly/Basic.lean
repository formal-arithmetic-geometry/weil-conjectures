/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Multiset.Powerset
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Characteristic polynomials along a filtration and under the linear-algebra operations

If an endomorphism `f` of a finite free module `V` preserves a submodule `W`, then the
characteristic polynomial of `f` factors as the product of the characteristic polynomials of the
restriction of `f` to `W` and of the endomorphism induced by `f` on `V ⧸ W`. Iterating this over a
filtration with graded pieces `gr_j` gives `det (1 - T f ∣ V) = ∏_j det (1 - T f ∣ gr_j)`.  This is
the characteristic-polynomial analogue of `LinearMap.det_eq_det_mul_det`, and is stated at the
same generality; Mathlib currently has only the direct-sum case `LinearMap.charpoly_prodMap`.

Over an algebraically closed field the eigenvalue multiset of an endomorphism `f`, counted with
multiplicity, is the multiset of roots `f.charpoly.roots` of its characteristic polynomial. The
second half of the file records how that multiset behaves under the standard operations: if `f`
has eigenvalues `α₁, …, α_r` and `g` has eigenvalues `β₁, …, β_t`, then `f ⊗ g` has eigenvalues
`α_i β_j`, the `s`-th exterior power `⋀^s f` has eigenvalues `α_{i₁} ⋯ α_{i_s}` for
`i₁ < ⋯ < i_s`, and the contragredient `(f⁻¹)^∨` of an invertible `f` has eigenvalues `α_i⁻¹`.
The last one splits into the transpose-invariance of the characteristic polynomial, which is
`LinearMap.charpoly_dualMap` in `WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix`, and
the inversion of the roots.

## Main declarations

* `LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ`: the characteristic polynomial of an
  endomorphism preserving a submodule is the product of those of the restriction to the submodule
  and of the induced endomorphism of the quotient.
* `LinearMap.charpoly_eq_one_of_subsingleton`: the characteristic polynomial of an
  endomorphism of the zero module is `1`.
* `LinearMap.charpoly_roots_tensorProduct`: the eigenvalues of a tensor product of endomorphisms
  are the pairwise products of the eigenvalues of the factors.
* `LinearMap.charpoly_roots_exteriorPower`: the eigenvalues of the `s`-th exterior power of an
  endomorphism are the products over the `s`-element sub-multisets of its eigenvalues.
* `LinearMap.charpoly_roots_dualMap_symm`: the eigenvalues of the contragredient of a linear
  automorphism are the inverses of its eigenvalues.

## Blueprint

`LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ` implements `sk-p-linear-filtration`;
`LinearMap.charpoly_roots_tensorProduct`, `LinearMap.charpoly_roots_exteriorPower` and
`LinearMap.charpoly_roots_dualMap_symm` implement `sk-p-linear-spectra`.
-/

@[expose] public section

open scoped TensorProduct

namespace LinearMap

section CommRing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Module.Free R V]
  [Module.Finite R V]

/-- If an endomorphism preserves a submodule `W` with `W` and `V ⧸ W` finite free, its
characteristic polynomial is the product of the characteristic polynomials of the induced
endomorphisms of `W` and of `V ⧸ W`.
(blueprint: `sk-p-linear-filtration`) -/
theorem charpoly_eq_charpoly_restrict_mul_charpoly_mapQ (f : V →ₗ[R] V) (W : Submodule R V)
    [Module.Free R W] [Module.Finite R W] [Module.Free R (V ⧸ W)] [Module.Finite R (V ⧸ W)]
    (hW : W ≤ W.comap f) :
    f.charpoly = (f.restrict hW).charpoly * (W.mapQ W f hW).charpoly := by
  sorry

/-- The characteristic polynomial of an endomorphism of the zero module is `1`. -/
theorem charpoly_eq_one_of_subsingleton [Nontrivial R] [Subsingleton V] (f : V →ₗ[R] V) :
    f.charpoly = 1 :=
  Polynomial.eq_one_of_monic_natDegree_zero f.charpoly_monic
    (f.charpoly_natDegree.trans Module.finrank_zero_of_subsingleton)

end CommRing

section IsAlgClosed

variable {K V W : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The eigenvalues of the tensor product of two endomorphisms are the pairwise products of their
eigenvalues, with multiplicity.
(blueprint: `sk-p-linear-spectra`) -/
theorem charpoly_roots_tensorProduct (f : V →ₗ[K] V) (g : W →ₗ[K] W) :
    (TensorProduct.map f g).charpoly.roots =
      (f.charpoly.roots ×ˢ g.charpoly.roots).map fun p ↦ p.1 * p.2 := by
  sorry

/-- The eigenvalues of the `s`-th exterior power of an endomorphism are the products of the
`s`-element sub-multisets of its eigenvalues.
(blueprint: `sk-p-linear-spectra`) -/
theorem charpoly_roots_exteriorPower (f : V →ₗ[K] V) (s : ℕ) :
    (exteriorPower.map s f).charpoly.roots =
      (f.charpoly.roots.powersetCard s).map Multiset.prod := by
  sorry

/-- The eigenvalues of the contragredient of a linear automorphism, that is the dual of its
inverse, are the inverses of its eigenvalues.
(blueprint: `sk-p-linear-spectra`) -/
theorem charpoly_roots_dualMap_symm (f : V ≃ₗ[K] V) :
    (f.symm : V →ₗ[K] V).dualMap.charpoly.roots =
      (f : V →ₗ[K] V).charpoly.roots.map fun a ↦ a⁻¹ := by
  sorry

end IsAlgClosed

end LinearMap
