module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Polynomial.Roots
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper
import Sheaf.AlgebraicGeometry.SnapperNumericalPolynomial
import Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny

/-! # Euler characteristics of integer tensor powers on an abelian variety

Source: Milne, Abelian Varieties, Chapter I, Theorem 11.1(b), printed p.54 (PDF p.60):
apply abelian Riemann--Roch to the divisor `nD` representing the integer tensor power.
(blueprint: lem-sfb-abelian-euler-tensor-homogeneity)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- On a positive-dimensional abelian variety over an algebraically closed field, the
Euler characteristic of every integer tensor power of an invertible sheaf is homogeneous
of degree the dimension. No ampleness or nondegeneracy is required.

Nonnegative powers use `Scheme.Modules.tensorPow`, whose zeroth power is the structure
sheaf. Negative powers use the same tensor powers of `Scheme.Modules.dual`, which is the
canonical tensor inverse for an invertible module. `Scheme.Modules.eulerChar` is the
integer-valued coherent Zariski Euler characteristic; properness makes the relevant
cohomology finite dimensional and zero in sufficiently high degrees.

Source: Milne, Abelian Varieties, Chapter I, Theorem 11.1(b), printed p.54 (PDF p.60).
(blueprint: lem-sfb-abelian-euler-tensor-homogeneity)

Proof plan:
1. The abelian variety is proper and finite type (`def-sc-abelian-variety`,
   `def-weil-proper-morphism`). A field is Noetherian, so
   `lem-weil-pbc-finite-type-over-noetherian` makes the variety Noetherian. Local rank-one
   frames (`def-sc-invertible-module`) make all signed tensor powers quasi-coherent and
   finite type. By `pqf-lem-coherent-ft-locnoeth` they are coherent, and
   `lem-pc-euler-characteristic-well-defined` gives the finite Euler sums.
2. Apply `lem-sc-snapper-numerical-polynomial` to the structure sheaf and the single
   invertible sheaf L. This gives P in Q[X] with P(n) = chi(L^n) for every integer n.
   Put c = chi(L), so P(1) = c.
3. The representing families in `lem-sfb-abelian-polarization-calculus` give
   phi_(L^n) = [n] composed with phi_L for positive n: pullback and tensor identify the
   difference family with the nth tensor power of the difference family of L, including
   its identity rigidification. Tensor is addition in the represented Picard functor.
   The dual abelian variety has the same dimension g.
4. By `lem-sc-isogeny-facts`, degree([n]) = n^(2g). Apply
   `lem-sfb-isogeny-postcomposition-degree`, including its zero convention when phi_L is
   not an isogeny. Then `lem-sfb-abelian-euler-degree-square` for L and L^n gives
   P(n)^2 = c^2 n^(2g) for every positive integer n.
5. The positive integers have distinct images in Q, so
   `lem-trf-polynomial-infinite-evaluation-identity` gives P^2 = c^2 X^(2g).
   Factor as (P - c X^g)(P + c X^g) = 0 in the domain Q[X]. Hence P = c X^g or
   P = -c X^g; evaluation at 1 removes the second possibility unless c = 0, when both
   coincide. Evaluate at every integer and use injectivity of Z into Q. This also gives
   the zero exponent, since g is positive. -/
theorem IsAbelianVariety.eulerChar_tensor_integer_power
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (g : ℕ) (hg : 1 ≤ g) (hdim : topologicalKrullDim A.left = (g : WithBot ℕ∞))
    (L : A.left.Modules) [L.IsInvertible] (n : ℤ) :
    (if 0 ≤ n then L.tensorPow n.toNat else L.dual.tensorPow (-n).toNat).eulerChar k =
      n ^ g * L.eulerChar k := by
  sorry

end AlgebraicGeometry
