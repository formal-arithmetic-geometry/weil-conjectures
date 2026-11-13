/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
import WeilConjectures.AlgebraicGeometry.EtaleGraphRefinementNormalization
import all WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

/-! # The diagonal normalization of the specified product-graph map

Source: Stacks Project, Tags 0F7C--0F7E, and the repeated-presentation diagonal.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The graph map comparing a compactification with itself only inserts R(id)_*
(Stacks, Tags 0F7C and 0F7E). -/
theorem etaleGraphComparison_diagonal
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    etaleGraphComparisonFromOpen A c (EtaleGraphPresentation.ofCompactification c) =
      (etaleGraphOpenNormalization A c).symm := by
  have hrho : rightDerivedLowerShriekOfCompactificationComparison
      (ModuleCat.{u + 1} A) (Compactification.Refinement.id c)
      (IsPullback.id_vert c.i) = 𝟙 _ := by
    let := unbounded_has_base_change A
    rw [← unbounded_refinement_comparison A]
    exact (unboundedFormalism A).refinementComparison_eq_id _ _ rfl
  rw [etaleGraphFromOpen_refinement A c c (Compactification.Refinement.id c)
    (IsPullback.id_vert c.i)]
  have he : asIso (rightDerivedLowerShriekOfCompactificationComparison
      (ModuleCat.{u + 1} A) (Compactification.Refinement.id c)
      (IsPullback.id_vert c.i)) = Iso.refl _ :=
    Iso.ext hrho
  rw [he, Iso.refl_trans]

end AlgebraicGeometry.Etale
