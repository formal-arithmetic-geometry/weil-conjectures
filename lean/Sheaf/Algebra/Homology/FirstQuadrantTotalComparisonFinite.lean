/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.QuasiIso
import Sheaf.CategoryTheory.DoubleComplexTotal

/-! # Comparison for a finite strip of rows

Source: Stacks Project, Homology, Section 12.25, finite filtration argument.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

/-- Column comparison when only finitely many rows can be nonzero.
Source: Stacks Project, Section 12.25 (Tags 012X and 0133), finite filtration argument.
(blueprint: lem-sc-finite-row-total-column-comparison).

Proof: filter both total complexes by the vertical degree, starting with the largest
possible degree N. The successive subquotients are the horizontal complexes in
vertical degree q, shifted by q, with the total differential's signs. The induced
map on each subquotient is a shift of the corresponding column map of the flipped
bicomplex, hence is a quasi-isomorphism by hf. The filtration starts at zero above
N and ends at the whole total complex at zero. Each filtration short exact sequence
is split on graded objects, because the diagonal is a finite direct sum. Apply the
long exact homology sequence and the five lemma at each successive step, descending
from N to zero. This proves the total map is a quasi-isomorphism. For N=0 there is
one quotient; no assumption about boundedness in the horizontal direction is used. -/
theorem quasiIso_totalMap_of_columns_of_finite_rows
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : K ⟶ L) (N : ℕ)
    (hK : ∀ p q : ℕ, N < q → IsZero ((K.X p).X q))
    (hL : ∀ p q : ℕ, N < q → IsZero ((L.X p).X q))
    (hf : ∀ q : ℕ, QuasiIso
      (((flipFunctor C (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map f).f q)) :
    QuasiIso (total.map f (ComplexShape.up ℕ)) := by
  sorry

end HomologicalComplex₂
