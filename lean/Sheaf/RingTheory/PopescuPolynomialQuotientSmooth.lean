/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.RingTheory.SingularIdeal
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.RingTheory.SingularIdealLocalizationSmooth

/-!
# The polynomial quotient used in separable Popescu preparation

Source: Stacks Project, proof of Lemma 07FE, first paragraph.
-/

@[expose] public section

universe u v

namespace Algebra

/-- The equations of the explicit quotient in Stacks, proof of Lemma 07FE.
(blueprint: lem-weil-pbc-popescu-polynomial-quotient-smooth). -/
noncomputable def popescuPolynomialRelations {A : Type v} [CommRing A] (d n : ℕ) {m : ℕ}
    (a : Fin m → A) (i : Fin d) : MvPolynomial (Fin d ⊕ (Fin d × Fin m)) A :=
  MvPolynomial.X (Sum.inl i) ^ n -
    ∑ j : Fin m, MvPolynomial.X (Sum.inr (i, j)) * MvPolynomial.C (a j)

/-- The actual polynomial quotient, before improving its presentation.
(blueprint: lem-weil-pbc-popescu-polynomial-quotient-smooth). -/
abbrev PopescuPolynomialQuotient {A : Type v} [CommRing A] (d n : ℕ) {m : ℕ}
    (a : Fin m → A) :=
  MvPolynomial (Fin d ⊕ (Fin d × Fin m)) A ⧸
    Ideal.span (Set.range (popescuPolynomialRelations d n a))

/-- The polynomial base map sends `X i` to the class of the corresponding variable.
(blueprint: lem-weil-pbc-popescu-polynomial-quotient-smooth). -/
noncomputable def popescuPolynomialBaseMap {k : Type u} {A : Type v}
    [CommRing k] [CommRing A] [Algebra k A] (d n : ℕ) {m : ℕ} (a : Fin m → A) :
    MvPolynomial (Fin d) k →ₐ[k] PopescuPolynomialQuotient d n a :=
  MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl i)))

/-- The explicit quotient is finitely presented over the polynomial base; its opens at
singular-ideal generators and at the base variables are smooth.
Source: Stacks Project, proof of Lemma 07FE, first paragraph.
(blueprint: lem-weil-pbc-popescu-polynomial-quotient-smooth).

Proof: write `P=A[X_i,Z_ij]` and impose the finitely many displayed relations. The
finite presentation of A over k, together with the finitely many Z variables and
relations, gives a finite presentation over R=k[X_i]. For each generator a_j,
A_(a_j) is smooth over k because a_j belongs to H_(A/k). Invert a_j and solve each
relation uniquely for Z_ij; this identifies B_(a_j) with a polynomial ring in the
remaining Z variables over A_(a_j)[X_i]. Smoothness follows by base change,
polynomial smoothness and composition. In B_(X_i), the equation X_i^n=Σ Z_ij a_j
shows that the images of all a_j generate the unit ideal. Smoothness is local on
this principal cover, so B_(X_i) is smooth over R. If m=0, that equation says
X_i^n=0; its localization is the zero ring, which is smooth over R. If d=0,
there are no relations or X opens and the construction is A itself. These
arguments apply also when A or a localization is the zero ring. -/
theorem popescuPolynomialQuotient_smooth
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [FinitePresentation k A] (d n : ℕ) (hn : 1 ≤ n) {m : ℕ} (a : Fin m → A)
    (ha : Ideal.span (Set.range a) = singularIdeal k A) :
    let B := PopescuPolynomialQuotient d n a
    letI := (popescuPolynomialBaseMap (k := k) d n a).toRingHom.toAlgebra
    FinitePresentation (MvPolynomial (Fin d) k) B ∧
      (∀ j : Fin m, Smooth (MvPolynomial (Fin d) k)
        (Localization.Away (algebraMap A B (a j)))) ∧
      ∀ i : Fin d, Smooth (MvPolynomial (Fin d) k)
        (Localization.Away
          (algebraMap (MvPolynomial (Fin d) k) B (MvPolynomial.X i))) := by sorry

end Algebra
