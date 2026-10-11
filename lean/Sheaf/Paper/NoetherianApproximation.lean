/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.MvPolynomial.Basic

/-! # Noetherian approximation of a relative global complete intersection

Source: Stacks Project, Algebra, Lemma Tag 00SU
(blueprint: lem-weil-pbc-relative-global-complete-intersection-noetherian-approximation).
-/

universe u

namespace Algebra

/-- Descend the specified complete-intersection presentation to a finite type subring.
Source: Stacks Project, Algebra, Lemma Tag 00SU
(blueprint: lem-weil-pbc-relative-global-complete-intersection-noetherian-approximation).

Proof, following the six DAG steps:
1. Generate a finite type subring by the coefficients of the relations, and form its
polynomial quotient. Polynomial scalar extension and tensor-quotient base change identify
its base change with the original quotient (`lem-weil-pbc-polynomial-scalar-extension`,
`lem-weil-pbc-tensor-quotient-base-change`, `def-weil-pbc-finite-type-algebra`).
2. Contract a prime of the original quotient to the coefficient model and both bases.
The fibre rings are nonzero, and tensor cancellation identifies one as the field extension
of the other. Faithful flatness makes the map of spectra surjective. Local dimension is
unchanged under field extension; taking suprema shows global dimensions agree, hence the
model fibre has dimension `n-c`. Use `lem-weil-pbc-tensor-cancel-base-change`,
`lem-weil-pbc-prime-in-image-iff-fibre-ring-nonzero`,
`lem-weil-pbc-field-extension-base-change-faithfully-flat`,
`lem-weil-pbc-faithfully-flat-surjective-spectrum`,
`lem-weil-pbc-dimension-at-point-field-extension`, and
`lem-weil-pbc-dimension-supremum-local-dimensions`.
3. Apply `lem-weil-pbc-fibre-dimension-neighborhood` at the contracted prime with its
actual local dimension. Obtain a principal open on which all nonzero fibres have dimension
at most `n-c`; its pullback contains the original prime
(`lem-weil-pbc-spec-localization-away-basic-open`).
4. Quasi-compactness gives finitely many such opens covering the original spectrum.
Lift their generators and a unit-ideal identity to polynomials, obtaining an identity
`1 - ∑ hⱼ Gⱼ = ∑ aᵢ fᵢ`. For the zero quotient take the empty cover and the identity
`1 = ∑ aᵢ fᵢ` (`lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`).
5. Enlarge the coefficient subring by the finitely many coefficients in this identity.
The identity now holds in the new model, so its principal opens cover its spectrum.
Fibre bounds persist under enlargement by polynomial and quotient base change, localization
base change (`lem-weil-pbc-algebra-localization-away-base-change`), field-extension invariance
of local dimension, and the supremum formula. Local dimension is unchanged on these opens
(`lem-weil-pbc-dimension-at-point-open-subspace`), giving the bound on every nonzero fibre.
6. If the new quotient is zero the condition is vacuous. Otherwise a nonzero fibre
forces `c ≤ n`. Each nonzero fibre is the quotient of a polynomial ring over its residue
field by these same `c` equations. The bound
`lem-weil-pbc-polynomial-quotient-dimension-lower-bound` gives dimension at least `n-c`.
Together with step 5 this gives equality, so take the enlarged subring.
-/
theorem exists_finiteType_subring_relativeGlobalCompleteIntersection
    (R : Type u) [CommRing R] (n c : ℕ)
    (f : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation f) :
    ∃ (R₀ : Subring R), Algebra.FiniteType ℤ R₀ ∧
      ∃ (f₀ : Fin c → MvPolynomial (Fin n) R₀),
        (∀ (i : Fin c) (d : Fin n →₀ ℕ),
          (MvPolynomial.coeff d (f i)) = (((MvPolynomial.coeff d (f₀ i)) : R₀) : R)) ∧
        IsRelativeGlobalCompleteIntersectionPresentation f₀ := by
  sorry

end Algebra
