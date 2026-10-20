/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.Algebra.Homology.FilteredPageLocalizationSetup
import Sheaf.Algebra.Homology.FilteredPageDescent
import Sheaf.Algebra.Homology.FilteredPageStationary

/-! # Localization of finite filtered pages

Source: Stacks Project, Tags 012K, 012M, 012O, 012P, 012W, 05S2 and 05S3.
(blueprint: lem-kun-filtered-page-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Filtered pages, filtered cohomology and the normalized stationary image abutment descend
to D_f(R). Bidegrees (a,b) cover the node's (a,n-a) by b=n-a. There is no cochain-degree bound.
Source: Stacks, Tags 012K, 012M, 012O, 012P, 012W, 05S1, 05S2, 05S3 and 04VK
(blueprint: lem-kun-filtered-page-localization).

Proof. The normalized model supplies the actual quotient-window page functor and
its representative, first-page and successor equations. Finite descending induction
through the short exact sequences of filtration steps proves graded comparison.
Filtered homotopy invariance and inversion of graded quasi-isomorphisms then give
`filteredPageDescent`, including the ordinary and graded derived comparisons.
The short exact sequence of the ambient quotient identifies the quotient image
with the graded cohomology image. Actual cycles characterize both stationary
comparisons and the normalized successor equation makes them compatible.
Naturality on generators extends through localization by eventual naturality;
finite descent through successor pages proves the square at every index stationary
for the endpoints. This gives `filteredPageStationary`. Combine the two records
field by field. No cochain-degree bound enters the proof. -/
theorem filteredPageLocalization (R : Type u) [CommRing R] :
    Nonempty (FilteredPageLocalizationData R) := by
  obtain ⟨d⟩ := filteredPageDescent R
  obtain ⟨s⟩ := filteredPageStationary R d
  exact ⟨{
    Sbar := d.Sbar
    eS := d.eS
    Hbar := d.Hbar
    eH := d.eH
    omega := d.omega
    eOmega := d.eOmega
    ordinaryCohomology := d.ordinaryCohomology
    ordinary_normalization := d.ordinary_normalization
    gradedDerived := d.gradedDerived
    gradedComparison := d.gradedComparison
    graded_chain := d.graded_chain
    page_one := d.page_one
    page_one_chain := d.page_one_chain
    homotopy_invariance := d.homotopy_invariance
    quasiIso_representatives := d.quasiIso_representatives
    quasiIso_pages := d.quasiIso_pages
    imageDerived := s.imageDerived
    imageComparison := s.imageComparison
    image_chain := s.image_chain
    bound := s.bound
    stationary_window := s.stationary_window
    comparison := s.comparison
    stationary_naturality := s.stationary_naturality
    stationary_graded_naturality := s.stationary_graded_naturality
    successor_agreement := s.successor_agreement
    successor_graded_agreement := s.successor_graded_agreement
  }⟩

end CategoryTheory
