/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
import WeilConjectures.AlgebraicGeometry.ValuativeSquareOfMemClosureRange
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Closedness of an immersion from valuative factorization

## References

* Stacks Project, Tags 02JQ, 01R8 and 01IQ
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A quasi-compact immersion whose valuation-ring maps factor whenever their generic
restrictions factor has closed image and is a closed immersion.
(Stacks, Tags 02JQ, 01R8, 01IQ) -/
theorem isClosed_range_and_isClosedImmersion_of_valuativeFactorization
    {Z S : Scheme.{u}} (j : Z ⟶ S) [QuasiCompact j] [IsImmersion j]
    (h : ∀ sq : ValuativeCommSq j,
      ∃ l : Spec (CommRingCat.of sq.R) ⟶ Z, l ≫ j = sq.i₂) :
    IsClosed (Set.range j) ∧ IsClosedImmersion j := by
  have hclosed : IsClosed (Set.range j) := by
    apply isClosed_of_closure_subset
    intro s hs
    obtain ⟨sq, hsq⟩ := exists_valuativeCommSq_of_mem_closure_range j hs
    obtain ⟨l, hl⟩ := h sq
    refine ⟨l (IsLocalRing.closedPoint sq.R), ?_⟩
    rw [← Scheme.Hom.comp_apply, hl, hsq]
  exact ⟨hclosed, IsClosedImmersion.of_isPreimmersion j hclosed⟩

end AlgebraicGeometry
