/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Smoothness after eliminating the auxiliary variables

Source: Stacks Project, proof of Lemma 07FE, first paragraph.
-/

@[expose] public section

universe u v

namespace Algebra

/-- Inverting one coefficient in the displayed relations yields a smooth algebra over
`k[X_i]`, provided the corresponding coefficient localization of `A` is smooth over `k`.

Source: Stacks Project, proof of Lemma 07FE, first paragraph.
(blueprint: lem-weil-pbc-popescu-polynomial-coefficient-localization-smooth).

Proof: fix `j`. Over `A_(a j)` each relation has an invertible coefficient of `Z_(i,j)`.
Solve it as `Z_(i,j) = (a j)⁻¹ * (X_i^n - Σ_(l ≠ j) Z_(i,l) a_l)`.
The quotient localized at `a j` is therefore canonically isomorphic, as a `k[X_i]`-algebra,
to the polynomial algebra in `Z_(i,l)` for `l ≠ j` over `A_(a j)[X_i]`.
Construct the forward map on all variables by the displayed formula and the inverse on the
remaining variables by their quotient classes. The equations show the two compositions
are identities. The base algebra `A_(a j)[X_i]` is smooth over `k[X_i]` by base change
of the assumed smooth map `k → A_(a j)`. Adjoining the remaining finitely many variables
is smooth, and composition and transport along the algebra equivalence give the result.
If `d = 0`, this is precisely the assumed smoothness. If `a j` is nilpotent, both localized
rings are zero and the same construction applies. The exponent may be zero; elimination
uses the invertibility of `a j`, not any condition on `n`. -/
theorem popescuPolynomialCoefficientLocalization_smooth
    {k : Type u} {A : Type v} [CommRing k] [CommRing A] [Algebra k A]
    (d n : ℕ) {m : ℕ} (a : Fin m → A) (j : Fin m)
    (hj : Smooth k (Localization.Away (a j))) :
    let P := MvPolynomial (Fin d ⊕ (Fin d × Fin m)) A
    let B := P ⧸ Ideal.span (Set.range (fun i : Fin d ↦
      MvPolynomial.X (Sum.inl i) ^ n -
        ∑ l : Fin m, MvPolynomial.X (Sum.inr (i, l)) * MvPolynomial.C (a l)))
    let f : MvPolynomial (Fin d) k →ₐ[k] B :=
      MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl i)))
    letI := f.toRingHom.toAlgebra
    Smooth (MvPolynomial (Fin d) k) (Localization.Away (algebraMap A B (a j))) := by sorry

end Algebra
