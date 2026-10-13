/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.CategoryTheory.FilteredComplexQuotientCoherence

/-! # Descent of filtered maps to coherent quotient pages

Source: Stacks Project, Homology, Tag 012K, lemma-functorial.
(blueprint: lem-weil-pbc-filtered-quotient-map).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A filtered map descends to quotient pages with representative-fixed comparisons.
This statement has no sheaves, augmented resolutions or first-page identifications.
Source: Stacks Project, Tag 012K, lemma-functorial.
(blueprint: lem-weil-pbc-filtered-quotient-map).

Proof. Choose the uniquely determined restrictions of b to the filtration steps.
The chain-map equation takes a representative whose differential belongs to the
(p+r)-th step to another such representative. The induced map on the graded quotient
therefore takes Z_r into Z'_r. The same equation takes the image of differentials
from the (p-r+1)-th step into the corresponding target image, and hence takes B_r
into B'_r. Apply the cokernel universal property to these inclusions and conjugate
by e and e' to obtain the page components. The representative differential equations
in the two coherence hypotheses show that these components commute with d_r:
precompose with the epimorphism from unquotiented cycle representatives and use
b.comm. At unrelated bidegrees both differentials vanish. For successor compatibility,
precompose with the epimorphism from Z_(r+1) onto the cycles of the r-page, followed
by the homology projection. The successor equations in the two coherence hypotheses
identify both composites with the induced map on Z_(r+1)/B_(r+1). Cancel this
composite epimorphism. These chain maps and successor squares define N; the cokernel
factorization equation gives its asserted action on every test object. Pullbacks of
epimorphisms suffice for local lifting, so no projectivity or finiteness is assumed. -/
theorem filteredComplex_quotient_map
    (K K' : CochainComplex C ℤ) (F : DecreasingFiltration K) (F' : DecreasingFiltration K')
    (E E' : CohomologicalSpectralSequence C 1)
    (e : ∀ (p q r : ℤ) (hr : 1 ≤ r),
      (E.page r hr).X (p, q) ≅ filteredComplexPageObject K F r (p, q))
    (e' : ∀ (p q r : ℤ) (hr : 1 ≤ r),
      (E'.page r hr).X (p, q) ≅ filteredComplexPageObject K' F' r (p, q))
    (hc : FilteredComplexQuotientCoherence K F E e)
    (hc' : FilteredComplexQuotientCoherence K' F' E' e')
    (b : K ⟶ K')
    (hb : ∀ p : ℤ, ∃ s : (F.step p : CochainComplex C ℤ) ⟶
        (F'.step p : CochainComplex C ℤ),
      s ≫ (F'.step p).arrow = (F.step p).arrow ≫ b) :
    ∃ N : E ⟶ E', ∀ (A : C) (p q r : ℤ) (hr : 1 ≤ r)
      (x : A ⟶ (F.step p : CochainComplex C ℤ).X (p + q))
      (y : A ⟶ (F'.step p : CochainComplex C ℤ).X (p + q))
      (z : A ⟶ (F.complexCycles p (p + q) r : C))
      (z' : A ⟶ (F'.complexCycles p (p + q) r : C)),
      x ≫ (F.step p).arrow.f (p + q) ≫ b.f (p + q) =
        y ≫ (F'.step p).arrow.f (p + q) →
      z ≫ (F.complexCycles p (p + q) r).arrow =
        x ≫ (F.complexQuotientπ p (p + 1) (by omega)).f (p + q) →
      z' ≫ (F'.complexCycles p (p + q) r).arrow =
        y ≫ (F'.complexQuotientπ p (p + 1) (by omega)).f (p + q) →
      z ≫ filteredComplexPageπ K F r (p, q) ≫ (e p q r hr).inv ≫
          (N.hom r hr).f (p, q) =
        z' ≫ filteredComplexPageπ K' F' r (p, q) ≫ (e' p q r hr).inv := by sorry

end CategoryTheory
