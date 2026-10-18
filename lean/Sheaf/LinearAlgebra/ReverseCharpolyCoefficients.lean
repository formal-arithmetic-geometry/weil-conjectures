/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Coefficients of the reverse characteristic polynomial

Source: the Weil conjectures blueprint, `sec-zeta-weil`, `sk-def-cohfamily`,
`def-weil-smooth-proper-cohomological-family`, final coefficient sentence
(blueprint: lem-weil-reverse-charpoly-coefficients).

The reverse characteristic polynomial is written as `F.charpolyRev`, the basis-free
construction supplied by `WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix`.
-/

@[expose] public section

universe u v

namespace LinearMap

/-- Source: the Weil conjectures blueprint, `sec-zeta-weil`, `sk-def-cohfamily`,
`def-weil-smooth-proper-cohomological-family`, final coefficient sentence
(blueprint: lem-weil-reverse-charpoly-coefficients).

For an arbitrary endomorphism of an `n`-dimensional vector space, `det (1 - T F)` has
constant coefficient one, degree at most `n`, and coefficient `(-1)^n det F` at `T^n`.
Its degree is `n` with that leading coefficient when `F` is invertible, and is less
than `n` otherwise.

Proof plan (the six steps of the DAG node):
1. Identify `det (1 - T F)` with `F.charpoly.reverse`, using
   `lem-weil-reverse-charpoly-eq-reverse` (`Matrix.reverse_charpoly` and
   `LinearMap.charpoly_toMatrix`), with the notions in `def-weil-characteristic-polynomial`
   and `def-weil-reverse-polynomial`.
2. By `lem-weil-charpoly-monic-degree`, the characteristic polynomial is monic of degree
   `n = Module.finrank K V`. By `lem-weil-charpoly-constant-coefficient-det`, its constant
   coefficient is `(-1)^n det F`, since the square of `(-1)^n` is one. This includes `n = 0`.
3. By `lem-weil-reverse-polynomial-coefficients`, reversing sends coefficient `n - j` to
   coefficient `j` for `j ≤ n`, and all coefficients beyond `n` are zero.
4. At `j = 0`, the resulting constant coefficient is the monic leading coefficient, one;
   equivalently evaluation at zero is one. Thus the reverse polynomial is nonzero.
5. The vanishing above `n` gives the degree bound, and the coefficient at `n` is the
   constant coefficient of the characteristic polynomial, namely `(-1)^n det F`.
6. This top coefficient is nonzero exactly when the determinant is nonzero, hence exactly
   when `F` is invertible by `lem-weil-endomorphism-invertible-iff-det-nonzero`.
   In that case it is the leading coefficient and the degree is `n`. Otherwise the
   coefficient at `n` vanishes, so the degree is strictly smaller than `n`.
The coefficient, degree, leading coefficient and determinant notions are those of
`def-weil-polynomial-coefficient` and `def-weil-endomorphism-determinant`. -/
theorem charpoly_reverse_coefficients {K : Type u} [Field K] {V : Type v}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (F : V →ₗ[K] V) :
    F.charpolyRev.coeff 0 = 1 ∧
      F.charpolyRev.natDegree ≤ Module.finrank K V ∧
      F.charpolyRev.coeff (Module.finrank K V) =
        (-1 : K) ^ Module.finrank K V * LinearMap.det F ∧
      (IsUnit F → F.charpolyRev.natDegree = Module.finrank K V ∧
        F.charpolyRev.leadingCoeff =
          (-1 : K) ^ Module.finrank K V * LinearMap.det F) ∧
      (¬ IsUnit F → F.charpolyRev.natDegree < Module.finrank K V) := by
  sorry

end LinearMap
