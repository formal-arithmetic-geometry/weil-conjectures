/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Characteristic polynomials along a filtration

If an endomorphism `f` of a finite-dimensional vector space `V` preserves a subspace `W`, then the
characteristic polynomial of `f` factors as the product of the characteristic polynomials of the
restriction of `f` to `W` and of the endomorphism induced by `f` on `V ⧸ W`. Iterating this over a
filtration with graded pieces `gr_j` gives `det (1 - T f ∣ V) = ∏_j det (1 - T f ∣ gr_j)`, and in
particular the eigenvalues of `f` on any subquotient occur among those of `f` on `V`.

Mathlib currently has only the direct-sum case `LinearMap.charpoly_prodMap` and the determinant
analogue `LinearMap.det_eq_det_mul_det`; the multiplicativity of the characteristic polynomial
along an arbitrary invariant subspace is not yet available.

## Main declarations

* `LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ`: the characteristic polynomial of an
  endomorphism preserving a subspace `W` is the product of those of the restriction to `W` and of
  the induced endomorphism of `V ⧸ W`.
* `Module.End.hasEigenvalue_of_subquotient`: a scalar acting on a nonzero invariant subquotient is
  an eigenvalue of the ambient endomorphism.
-/

@[expose] public section

section Filtration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Blueprint `sk-p-linear-filtration`: Characteristic polynomials along a filtration. If an
endomorphism preserves a subspace, its characteristic polynomial is the product of the
characteristic polynomials of the induced endomorphisms of the subspace and of the quotient. -/
theorem LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ
    (f : V →ₗ[K] V) (W : Submodule K V) (hW : W ≤ W.comap f) :
    f.charpoly = (f.restrict hW).charpoly * (W.mapQ W f hW).charpoly := by
  sorry

/-- Blueprint `sk-p-linear-filtration`: Characteristic polynomials along a filtration. If a scalar
`c` acts on a nonzero invariant subquotient `S ⧸ U` of `V`, then `c` is an eigenvalue of the
endomorphism on all of `V`. -/
theorem Module.End.hasEigenvalue_of_subquotient (f : Module.End K V) {U S : Submodule K V}
    (hUS : U ≤ S) (hne : U ≠ S) (hU : U ≤ U.comap f) (hS : S ≤ S.comap f) (c : K)
    (hc : ∀ x ∈ S, f x - c • x ∈ U) : f.HasEigenvalue c := by
  sorry

end Filtration
