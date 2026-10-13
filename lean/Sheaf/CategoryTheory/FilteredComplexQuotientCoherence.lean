/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Sheaf.CategoryTheory.FilteredComplexPageDifferential

/-! # Representative compatibility of quotient spectral sequences

Source: Stacks Project, Homology, Tag 012K, lemma-spectral-sequence-filtered-complex.
(blueprint: def-weil-pbc-filtered-quotient-coherence).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Compatibility with the concrete differential and the successor quotient map.
The successor equation is imposed on every test-object representative, and therefore
fixes the homology isomorphism rather than merely asserting that one exists.
Source: Stacks Project, Tag 012K, lemma-spectral-sequence-filtered-complex.
(blueprint: def-weil-pbc-filtered-quotient-coherence). -/
structure FilteredComplexQuotientCoherence
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (E : CohomologicalSpectralSequence C 1)
    (e : ∀ (p q r : ℤ) (hr : 1 ≤ r),
      (E.page r hr).X (p, q) ≅ filteredComplexPageObject K F r (p, q)) : Prop where
  differential : ∀ (r : ℤ) (hr : 1 ≤ r),
    ∃ (D : FilteredComplexPageDifferential K F r) (a : E.page r hr ≅ D.page),
      ∀ p q : ℤ, a.hom.f (p, q) = (e p q r hr).hom
  successor : ∀ (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
    (hZ : F.complexCycles p (p + q) (r + 1) ≤ F.complexCycles p (p + q) r)
    (A : C) (x : A ⟶ (F.complexCycles p (p + q) (r + 1) : C))
    (z : A ⟶ (E.page r hr).cycles (p, q)),
    z ≫ (E.page r hr).iCycles (p, q) =
      x ≫ Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ K F r (p, q) ≫
        (e p q r hr).inv →
    z ≫ (E.page r hr).homologyπ (p, q) ≫ (E.iso r (r + 1) (p, q) rfl hr).hom ≫
        (e p q (r + 1) (by omega)).hom =
      x ≫ filteredComplexPageπ K F (r + 1) (p, q)

end CategoryTheory
