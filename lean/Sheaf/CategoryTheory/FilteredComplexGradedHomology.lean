/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients

/-!
# Homology of the initial graded page

Source: Stacks Project, Homology, Tag 012K, the page-one calculation
(blueprint: lem-sp-filtered-complex-graded-homology).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Homology of any page-zero complex identified with the associated graded complex.
Source: Stacks Project, Homology, Tag 012K, displayed Z and B formulas and the
page-one assertion of `lemma-spectral-sequence-filtered-complex`.
(blueprint: lem-sp-filtered-complex-graded-homology).

Proof. In degree n = p+q the differential of gr^p K is induced from K.d.
Its kernel consists of the classes represented in F^p K^n whose differential lies
in F^(p+1) K^(n+1). Its image from degree n-1 consists of classes represented by
d(F^p K^(n-1)). The quotient projection from F^p K has kernel F^(p+1) K, so these
subobjects of gr^p K are precisely complexCycles p n 1 and complexBoundaries p n 1,
respectively, including the sums with F^(p+1) in their definitions. Thus d squared
= 0 gives the required containment, and homology, the cokernel of the inclusion
of image into kernel, is the stated quotient. The isomorphisms e and their
compatibility with outgoing differentials identify the short complex at (p,q)
with that of gr^p K at n, also for its incoming differential at (p,q-1).
The induced homology isomorphism gives the assertion for P.
-/
theorem filteredComplex_graded_homology
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (P : HomologicalComplex C (ComplexShape.up' (⟨0, 1⟩ : ℤ × ℤ)))
    (e : ∀ p q : ℤ, P.X (p, q) ≅ (F.gradedPiece p).X (p + q))
    (hd : ∀ p q : ℤ, P.d (p, q) (p, q + 1) ≫ (e p (q + 1)).hom =
      (e p q).hom ≫ (F.gradedPiece p).d (p + q) (p + (q + 1)))
    (p q : ℤ) :
    ∃ hBZ : F.complexBoundaries p (p + q) 1 ≤ F.complexCycles p (p + q) 1,
      Nonempty (P.homology (p, q) ≅ cokernel (Subobject.ofLE _ _ hBZ)) := by
  sorry

end CategoryTheory
