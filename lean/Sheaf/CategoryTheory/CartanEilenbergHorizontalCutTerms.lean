/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Injective terms in the horizontal good cut

Source: Stacks Project, Derived Categories, Tag 015X.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- The horizontal good cut retains first-quadrant support and termwise injectivity.
Source: Stacks Project, Tag 015X, second filtration.
(blueprint: lem-sp-ce-horizontal-cut-terms).

Proof. Below q use the canonical component isomorphism to I. In column q use the
canonical isomorphism to the horizontal cycles. These are injective by the two
injectivity conditions of a Cartan--Eilenberg resolution. Above q the cut is zero.
For a negative horizontal degree, q >= 0 puts it strictly below q, where the cut
agrees with I and hence vanishes. -/
theorem cartanEilenberg_horizontal_cut_terms
    {A : Type u} [Category.{v} A] [Abelian A]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (hzero : ∀ p : ℤ, p < 0 → IsZero (I.X p))
    (hterms : ∀ (p : ℤ) (r : ℕ), Injective ((I.X p).X r))
    (hcycles : ∀ (p : ℤ) (r : ℕ), Injective ((I.cycles p).X r))
    (q : ℤ) (hq : 0 ≤ q) :
    (∀ p : ℤ, p < 0 → IsZero ((CochainComplex.truncLE I q).X p)) ∧
      (∀ (p : ℤ) (r : ℕ), Injective (((CochainComplex.truncLE I q).X p).X r)) := by
  constructor
  · intro p hp
    exact (CochainComplex.truncLEXIso I q p (by omega)).isZero_iff.mpr (hzero p hp)
  · intro p r
    by_cases hp : p < q
    · exact Injective.of_iso
        ((HomologicalComplex.eval A (ComplexShape.up ℕ) r).mapIso
          (CochainComplex.truncLEXIso I q p hp)).symm (hterms p r)
    by_cases heq : p = q
    · subst p
      exact Injective.of_iso
        ((HomologicalComplex.eval A (ComplexShape.up ℕ) r).mapIso
          (CochainComplex.truncLEXIsoCycles I q)).symm (hcycles q r)
    · exact ((HomologicalComplex.eval A (ComplexShape.up ℕ) r).map_isZero
        (CochainComplex.isZero_of_isStrictlyLE
          (CochainComplex.truncLE I q) q p (by omega))).injective

end CategoryTheory
