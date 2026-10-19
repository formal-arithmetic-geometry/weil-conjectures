/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Diagonal root invariants and the nonnegative exponent lattice

Source: Illusie--Laszlo--Orgogozo, Exposé IX, Proposition 2.1, printed p. 133,
and Exposé VI, §§2.2--2.3 (blueprint: lem-per-diagonal-root-invariant-monoid-algebra).

The lattice consists of rational exponent vectors `q = a/n`.  The root monomial
attached to `q` is `x^(nq)`, and the inclusion of `ℕ^r` is the literal inclusion
of the nonnegative integral vectors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The parameter-root quotient used in the diagonal invariant lemma.
Source: ILO IX 2.1, printed p. 133 (blueprint: lem-per-diagonal-root-invariant-monoid-algebra). -/
def diagonalRootIdeal (A : Type u) [CommRing A] (n : ℕ) (r : ℕ)
    (t : Fin r → A) : Ideal (MvPolynomial (Fin r) A) :=
  Ideal.span (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i)))

/-- The algebra obtained by adjoining the prescribed `n`th roots.
Source: ILO IX 2.1, printed p. 133 (blueprint: lem-per-diagonal-root-invariant-monoid-algebra). -/
abbrev diagonalRootAlgebra (A : Type u) [CommRing A] (n : ℕ) (r : ℕ)
    (t : Fin r → A) := (MvPolynomial (Fin r) A ⧸ diagonalRootIdeal A n r t)

/-- The image of a polynomial variable in the parameter-root quotient.
Source: ILO IX 2.1, printed p. 133 (blueprint: lem-per-diagonal-root-invariant-monoid-algebra). -/
def diagonalRootGenerator (A : Type u) [CommRing A] (n : ℕ) (r : ℕ)
    (t : Fin r → A) (i : Fin r) : diagonalRootAlgebra A n r t :=
  Ideal.Quotient.mk (diagonalRootIdeal A n r t) (MvPolynomial.X i)

/--
Let `A` be a commutative ring, `n ≥ 1` invertible in `A`, and `ζ` an `n`th root of
unity with all nontrivial powers separated by units.  For a diagonal subgroup `H`
of `(ℤ/nℤ)^r`, the invariant subring of the parameter-root quotient is the monoid
base change for the nonnegative invariant exponent lattice. The map on monomials
is `z^q ↦ x^(nq)`. The algebra structures are characterized on all monomials by
`hbase` and `hinclusion`, so neither structure map is arbitrary.

Source: ILO, Exposé IX, Proposition 2.1 proof, printed p. 133, together with
Exposé VI 2.2--2.3, printed pp. 72--73 (blueprint: lem-per-diagonal-root-invariant-monoid-algebra).

Proof (following the eight steps of the DAG):
1. The congruence lattice contains the integral vectors. Thus `P` includes injectively
in `Q` and `nQ` lies in `P`. Reduction of numerator vectors modulo `n` embeds the
quotient by integral vectors in the finite group `(ℤ/nℤ)^r` and kills its `n`th multiple.
2. Divide each nonnegative numerator coordinate by `n`. Every element of `Q` is
uniquely `m + b/n` for `m ∈ P` and an invariant residue vector `0 ≤ b_i < n`.
These finitely many residues and the coordinate vectors generate `Q`. Every element
of `L` is a difference of nonnegative elements, giving the canonical group-completion
isomorphism. Nonnegativity is preserved on dividing by a positive integer, proving
saturation. An element and its negative are both nonnegative only at zero, proving sharpness.
3. Handle the zero coefficient ring separately. Otherwise successive polynomial
quotients by the monic polynomials `X_i^n - t_i` have the power bases supplied by
`lem-weil-pbc-monic-quotient-free` (`AdjoinRoot.powerBasis'`). Induction gives the
basis of root monomials with all exponents less than `n`; evaluation and quotient
maps are those of `def-weil-pbc-mv-polynomial-ring` and
`def-weil-pbc-algebra-hom-quotient`.
4. Each such monomial is an eigenvector for the specified diagonal action. For a
nontrivial character choose its residue `c` with `1 ≤ c < n`. The unit `1 - ζ^c`
forces its coefficient in any invariant element to vanish. The invariant residue
monomials therefore form an `A`-basis of the fixed subalgebra.
5. The unique residue decomposition in step 2 similarly writes `ℤ[Q]` freely over
`ℤ[P]` on the invariant residue monomials, using the finite-support definition
of `AddMonoidAlgebra`; this is a module decomposition, not a monoid product.
6. Base change this basis by `lem-weil-pbc-free-module-base-change-free`
(`Module.Basis.baseChange`). The monomial map `z^q ↦ x^(nq)` is multiplicative,
is invariant by the defining congruences, and agrees on `ℤ[P]` with evaluation at
`t`. The universal property `lem-weil-pbc-algebra-tensor-pushout-universal-property`
then supplies the balanced algebra map sending `a ⊗ z^q` to `a x^(nq)`.
7. This map sends the basis of step 6 to the basis of step 4 with the same index
set. The inverse sends each invariant basis monomial back to its corresponding
pure tensor. Thus it is an algebra isomorphism. The balancing relation identifies
`1 ⊗ z^(e_i)` with `t_i ⊗ 1`. Since `nq ∈ P`, taking the `n`th power of the
monomial formula gives `c_q^n = ∏ i, t_i^(nq_i)`.
8. For `r = 0` the residue set consists of the empty tuple and the map is the
identity of `A`. For `n = 1` the lattice is integral, `Q = P`, and the quotient
relations identify each root with its parameter. Zero or zero-divisor parameters
do not affect either power basis; cancellation only uses the units `1 - ζ^c`.
-/
theorem diagonal_root_invariant_monoid_algebra
    (A : Type u) [CommRing A]
    (n : ℕ) (hn : 1 ≤ n) (hnA : IsUnit (n : A))
    (ζ : Aˣ) (hζ : (ζ : A) ^ n = 1)
    (hζsep : ∀ a : ℕ, 1 ≤ a → a < n → IsUnit (1 - (ζ : A) ^ a))
    (r : ℕ) (t : Fin r → A)
    (H : AddSubgroup (Fin r → ZMod n))
    (L : AddSubgroup (Fin r → ℚ))
    (hL : ∀ q : Fin r → ℚ,
      q ∈ L ↔ ∃ a : Fin r → ℤ,
        (∀ i : Fin r, q i = (a i : ℚ) / (n : ℚ)) ∧
          ∀ h : H, ∑ i : Fin r, (h.1 i) * (a i : ZMod n) = 0)
    (P : AddSubmonoid (Fin r → ℚ))
    (hP : ∀ q : Fin r → ℚ,
      q ∈ P ↔ ∀ i : Fin r, ∃ a : ℕ, q i = (a : ℚ))
    (Q : AddSubmonoid (Fin r → ℚ))
    (hQ : ∀ q : Fin r → ℚ, q ∈ Q ↔ q ∈ L ∧ ∀ i : Fin r, 0 ≤ q i)
    (K : AddSubgroup L)
    (hK : ∀ q : L, q ∈ K ↔ ∀ i : Fin r, ∃ a : ℤ, q.1 i = (a : ℚ))
    (exp : Q → Fin r → ℕ)
    (hexp : ∀ q : Q, ∀ i : Fin r, (n : ℚ) * q.1 i = (exp q i : ℚ))
    [Algebra (AddMonoidAlgebra ℤ P) A]
    [Algebra (AddMonoidAlgebra ℤ P) (AddMonoidAlgebra ℤ Q)]
    (hbase : ∀ (p : P) (a : Fin r → ℕ),
      (∀ i : Fin r, p.1 i = (a i : ℚ)) →
        algebraMap (AddMonoidAlgebra ℤ P) A (AddMonoidAlgebra.single p 1) =
          ∏ i : Fin r, t i ^ a i)
    (hinclusion : ∀ (p : P) (q : Q), p.1 = q.1 →
      algebraMap (AddMonoidAlgebra ℤ P) (AddMonoidAlgebra ℤ Q)
        (AddMonoidAlgebra.single p 1) = AddMonoidAlgebra.single q 1)
    [MulSemiringAction (Multiplicative H) (diagonalRootAlgebra A n r t)]
    [SMulCommClass (Multiplicative H) A (diagonalRootAlgebra A n r t)]
    (hgen : ∀ h : H, ∀ i : Fin r,
      (Multiplicative.ofAdd h) • diagonalRootGenerator A n r t i =
        ((ζ : A) ^ ((h.1 i).val : ℕ)) • diagonalRootGenerator A n r t i) :
    IsFineSaturatedMonoid (Multiplicative Q) ∧
    (∀ q : Q, IsUnit (Multiplicative.ofAdd q) → q = 0) ∧
    (∃ g : Additive (Algebra.GrothendieckGroup (Multiplicative Q)) ≃+ L,
      ∀ q : Q, (g (Additive.ofMul
        (Algebra.GrothendieckGroup.of (Multiplicative.ofAdd q)))).1 = q.1) ∧
    (Finite (L ⧸ K)) ∧
    (∀ b : L, n • QuotientAddGroup.mk' K b = 0) ∧
    (∃ ι : P →+ Q, Function.Injective ι ∧ ∀ p : P, (ι p).1 = p.1) ∧
    (∀ q : Q, ∃ p : P, p.1 = fun i ↦ (n : ℚ) * q.1 i) ∧
    ∃ e :
        (A ⊗[AddMonoidAlgebra ℤ P] AddMonoidAlgebra ℤ Q) ≃ₐ[A]
          FixedPoints.subalgebra A (diagonalRootAlgebra A n r t) (Multiplicative H),
      (∀ (a : A) (q : Q),
        (e (a ⊗ₜ[AddMonoidAlgebra ℤ P]
          (AddMonoidAlgebra.single q 1)) : diagonalRootAlgebra A n r t) =
          (algebraMap A (diagonalRootAlgebra A n r t) a) *
            ∏ i : Fin r, (diagonalRootGenerator A n r t i) ^ exp q i) ∧
      (∀ (i : Fin r) (q : Q), q.1 = (fun j : Fin r ↦ if j = i then 1 else 0) →
        (e (1 ⊗ₜ[AddMonoidAlgebra ℤ P] AddMonoidAlgebra.single q 1) :
          diagonalRootAlgebra A n r t) = algebraMap A (diagonalRootAlgebra A n r t) (t i)) ∧
      (∀ q : Q,
        (e (1 ⊗ₜ[AddMonoidAlgebra ℤ P] AddMonoidAlgebra.single q 1) :
          diagonalRootAlgebra A n r t) ^ n =
            algebraMap A (diagonalRootAlgebra A n r t) (∏ i : Fin r, t i ^ exp q i)) := by
  sorry

end AlgebraicGeometry
