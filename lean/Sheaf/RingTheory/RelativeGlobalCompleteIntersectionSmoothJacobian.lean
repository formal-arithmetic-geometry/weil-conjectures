/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation
public import Sheaf.RingTheory.SingularIdeal
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The Jacobian criterion for a relative global complete intersection

Source: Stacks Project, Algebra, Lemma 00TE
(blueprint: lem-weil-pbc-relative-global-complete-intersection-smooth-jacobian).
-/

@[expose] public section

universe v

namespace Algebra

/-- A relative global complete intersection is smooth at a prime precisely when some maximal
Jacobian minor avoids that prime. A strictly increasing map `i : Fin c → Fin n` lists a subset
of size `c` in increasing order; rows of the determinant are equations and columns are `i k`.
Source: Stacks Project, Algebra, Lemma 00TE
(blueprint: lem-weil-pbc-relative-global-complete-intersection-smooth-jacobian).

Proof:
1. The conormal-free lemma 00SV identifies the conormal module with the free module on the
   equations. Its differential has entries given by their partial derivatives. Its selected
   row minors are the transposes of the displayed Jacobian minors, so have the same determinant;
   determinants commute with the quotient and localization maps by the Leibniz formula.
2. If smooth at the prime, choose `g` outside it with smooth principal localization. The
   smooth-localization-conormal-split lemma gives a left inverse to this localized differential.
   The localized conormal module has the localized equation basis, so its matrix has a left
   inverse over the localization.
3. This localization is nonzero since `g` avoids a prime. If `c > n`, Cauchy--Binet says the
   determinant of the product with its left inverse is zero, contradicting its value one.
4. The matrix-left-inverse-minors lemma 07DQ expresses one as a linear combination of maximal
   minors. If all minors were in the prime, clearing the finitely many powers of `g` in the
   denominators would put a power of `g` in the prime, a contradiction.
5. Conversely choose a minor with image `g` outside the prime. The principal-localization
   presentation lemma 08JZ presents the localization by adjoining `y` and the equation `g_I y-1`.
6. Rename variables to place the selected `c` variables first, followed by `y` and the remaining
   variables. Renaming commutes with formal partial derivatives by the monomial formula.
7. The enlarged Jacobian block is lower triangular, with diagonal blocks the chosen Jacobian
   and `g_I`. The block-triangular determinant lemma gives determinant `g_I^2`; its image in
   the localization is a unit. Thus this is a standard smooth presentation (Definition 00T6).
8. Standard smooth implies smooth by 00T7. The chosen `g` outside the prime witnesses smoothness
   at the prime, proving the reverse implication. -/
theorem isSmoothAtPrime_iff_exists_jacobian_minor
    (R : Type v) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    (hci : IsRelativeGlobalCompleteIntersectionPresentation f)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) :
    IsSmoothAtPrime R q ↔
      ∃ i : Fin c → Fin n, StrictMono i ∧
        Ideal.Quotient.mk (Ideal.span (Set.range f))
          (Matrix.det (fun j k : Fin c ↦ MvPolynomial.pderiv (i k) (f j))) ∉ q.asIdeal := by
  sorry

end Algebra
