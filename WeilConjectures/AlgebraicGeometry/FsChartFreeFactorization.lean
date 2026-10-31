/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.QuotientGroup.Basic

import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import WeilConjectures.LinearAlgebra.Matrix.CauchyBinet

/-!
# Free factorization of an injective fs chart

Source: Illusie--Laszlo--Orgogozo, Exposé VI, Proposition 1.9 and Exposé VIII,
3.1.1--3.1.2, 3.1.9--3.1.10 (blueprint: lem-trf-fs-chart-free-factorization).

## Main statements

* `exists_fs_chart_free_factorization` states the free-generator factorization of an injective
  homomorphism of fine saturated commutative monoids with torsion-free group cokernel.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v

namespace AlgebraicGeometry

/-- An injective fs chart with torsion-free group cokernel factors through a free
monoid chart with the same group completion. The finite product has componentwise
addition. `Multiplicative` only changes notation when applying the existing fs predicate.

Source: Illusie--Laszlo--Orgogozo, Exposé VI, Proposition 1.9, printed p. 71;
Exposé VIII, 3.1.1--3.1.2, 3.1.9--3.1.10, printed pp. 98--99, and 3.1.17, p. 101
(blueprint: lem-trf-fs-chart-free-factorization). The general factorization is the
agent-supplied algebraic refinement recorded in the node, rather than a verbatim ILO lemma.

Proof:
1. Put `G = Q^gp`, `H = range g^gp`, `L = G/H`, and `S = image(Q → L)`.
   Finite monoid generators of `Q` generate `L` as a group. By
   `lem-trf-fg-torsionfree-group-free`, the finitely generated torsion-free group `L`
   has a finite integer basis, identifying it with `ℤ^r`.
2. `S` is saturated. If `nℓ` is the image of `q` and `x` lifts `ℓ`, write
   `nx = q + g(a) - g(b)` with `a,b` in `P`. Then
   `n(x + g(b)) = q + g(a) + (n-1)g(b)` lies in `Q`. Saturation of `Q` gives
   `x + g(b)` in `Q`, so `ℓ` belongs to `S`.
3. If `r = 0`, take the empty basis. Otherwise the matrix `B` of a finite generating
   family of `S` admits an integer right inverse `C`, since this family generates `L`.
   Cauchy--Binet (`lem-weil-pbc-cauchy-binet`) applied to `BC = 1` supplies a tuple
   in `S` with nonzero determinant, including the check that there are at least `r` columns.
4. Choose such a tuple with least positive absolute determinant `D`. This uses the
   integer determinant of `def-weil-pbc-matrix-determinant` and well-ordering of `ℕ`.
5. If its columns form a proper sublattice, choose an integer vector `y` outside it.
   The adjugate identity (`lem-weil-pbc-matrix-adjugate-identity`) gives rational
   coordinates `b = A⁻¹y`. Set `z_i = floor(b_i)`, `a = b-z`, and `x = y-Az = Aa`.
   Here `x` is integral, `0 ≤ a_i < 1`, and some `a_j` satisfies `0 < a_j < 1`.
6. A positive common denominator `N` gives `Nx = ∑ (Na_i)v_i` in `S`.
   Step 2 gives `x` in `S`. Replace column `j` of `A` by `x`. The replacement matrix
   has determinant `a_j det(A)`: factor it as `AE`, use Cauchy--Binet in the square
   case and the Leibniz formula to compute `det(E) = a_j`. Its positive absolute
   determinant is smaller than `D`, a contradiction.
7. Thus the columns generate the integer lattice and are independent, so they give
   unique integer coordinates. Lift each column from `S` to an element `q_i` of `Q`.
8. Define `φ(x,m) = g^gp(x) + ∑ m_i[q_i]`. Applying the quotient map proves its
   injectivity using basis-coordinate uniqueness and injectivity of `g^gp`. To prove
   surjectivity, subtract the basis expansion of any quotient class; the remainder
   belongs to `H`. The same calculation handles rank zero.
9. Restrict this formula to `P × ℕ^r` to obtain `h`. Integrality of `P,Q` and
   injectivity of `ℕ^r → ℤ^r` show `h` is injective. The product universal property
   identifies `(P × ℕ^r)^gp` with `P^gp × ℤ^r`: maps out are determined by the
   restriction to `P` and the coordinate generators. The displayed formula therefore
   makes `φ` precisely the induced group-completion map of `h`. -/
theorem exists_fs_chart_free_factorization {P : Type u} {Q : Type v}
    [AddCommMonoid P] [AddCommMonoid Q]
    (hP : IsFineSaturatedMonoid (Multiplicative P))
    (hQ : IsFineSaturatedMonoid (Multiplicative Q)) (g : P →+ Q)
    (hg : Function.Injective (Algebra.GrothendieckAddGroup.lift
      ((Algebra.GrothendieckAddGroup.of (M := Q)).comp g)))
    (htorsion : ∀ (n : ℕ) (ℓ : Algebra.GrothendieckAddGroup Q ⧸
      (Algebra.GrothendieckAddGroup.lift
        ((Algebra.GrothendieckAddGroup.of (M := Q)).comp g)).range),
      0 < n → n • ℓ = 0 → ℓ = 0) :
    ∃ (r : ℕ) (q : Fin r → Q) (h : P × (Fin r → ℕ) →+ Q)
      (φ : Algebra.GrothendieckAddGroup P × (Fin r → ℤ) ≃+
        Algebra.GrothendieckAddGroup Q),
      (∀ (ℓ : Algebra.GrothendieckAddGroup Q ⧸
          (Algebra.GrothendieckAddGroup.lift
            ((Algebra.GrothendieckAddGroup.of (M := Q)).comp g)).range),
        ∃! m : Fin r → ℤ,
          ℓ = ∑ i, m i • QuotientAddGroup.mk (Algebra.GrothendieckAddGroup.of (q i))) ∧
        (∀ (p : P) (n : Fin r → ℕ), h (p, n) = g p + ∑ i, n i • q i) ∧
        Function.Injective h ∧
        (∀ (x : Algebra.GrothendieckAddGroup P) (m : Fin r → ℤ),
          φ (x, m) = Algebra.GrothendieckAddGroup.lift
            ((Algebra.GrothendieckAddGroup.of (M := Q)).comp g) x +
              ∑ i, m i • Algebra.GrothendieckAddGroup.of (q i)) := by
  sorry

end AlgebraicGeometry
