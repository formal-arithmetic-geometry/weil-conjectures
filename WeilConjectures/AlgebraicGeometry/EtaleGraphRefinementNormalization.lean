/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
import WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphMiddleTransport
import WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphSideTransport

/-! # Normalization of a graph map along one Cartesian proper refinement

Source: Stacks Project, Tags 0F7C--0F7E and the unit--open-base-change formula in
`LowerShriekIndependenceUnbounded.lean`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The graph map from a compactification to its Cartesian proper refinement is the
specified refinement map, followed by restoration of the initial identity direct image.
Source: Stacks Tags 0F7C--0F7E; `LowerShriekIndependenceUnbounded.lean`, refinement map. -/
theorem etaleGraphFromOpen_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (s r : Compactification f)
    (rs : r.Refinement s) (hs : IsPullback r.i (𝟙 X) rs.hom s.i) :
    etaleGraphComparisonFromOpen A s (EtaleGraphPresentation.ofCompactification r) =
      asIso (rightDerivedLowerShriekOfCompactificationComparison
        (ModuleCat.{u + 1} A) rs hs) ≪≫ (etaleGraphOpenNormalization A r).symm := by
  obtain ⟨h₁, h₂⟩ := etaleRefinementGraphSideTransport A s r rs hs
  have hm := etaleRefinementGraphMiddleTransport A s r rs hs
  let b₁ := locallyClosedGraphSide₁ (𝟙 X) r.i r.g s.i s.g
    (EtaleRefinementGraph.equation s r) A
  let b₂ := locallyClosedGraphSide₂ (𝟙 X) r.i r.g s.i s.g
    (EtaleRefinementGraph.equation s r) A
  calc
    _ = b₁ ≪≫ EtaleRefinementGraph.middle s r A ≪≫ b₂.symm := by
      change locallyClosedGraphIso (𝟙 X) r.i r.g s.i s.g
        (EtaleRefinementGraph.equation s r) A = _
      simp only [locallyClosedGraphIso, EtaleRefinementGraph.middle,
        b₁, b₂, EtaleRefinementGraph.s₁, EtaleRefinementGraph.s₂,
        EtaleRefinementGraph.b₁, EtaleRefinementGraph.b₂, EtaleRefinementGraph.p,
        Iso.trans_assoc]
    _ = (b₁ ≪≫ EtaleRefinementGraph.transport₁ s r rs A hs) ≪≫
        (b₂ ≪≫ EtaleRefinementGraph.transport₂ s r rs A).symm := by
      rw [← hm]
      simp only [Iso.trans_symm, Iso.trans_assoc, Iso.self_symm_id_assoc]
    _ = _ := by rw [h₁, h₂]

end AlgebraicGeometry.Etale
