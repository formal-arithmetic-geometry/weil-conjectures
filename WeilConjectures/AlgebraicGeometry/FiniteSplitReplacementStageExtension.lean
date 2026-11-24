/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStage
public import WeilConjectures.AlgebraicGeometry.EtaleHypercover
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementGeometry
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementRelativeCover
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementBoundaryAttachment

/-! The finite successor step in the split replacement construction. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

/-- A finite replacement stage `A` of degree `n` over an étale hypercover `K` extends to one of
degree `n + 1` restricting to `A` (Stacks, Tags 0DAV, 01GJ, 094K). -/
theorem exists_replacement_stage_extension
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject X.Etale) (hK : IsEtaleHypercover K)
    (n : ℕ) (A : FiniteSplitReplacementStage K n) :
    ∃ B : FiniteSplitReplacementStage K (n + 1), B.restrict n (Nat.le_succ n) = A := by
  obtain ⟨Q⟩ := exists_replacement_boundary A.U
  obtain ⟨N, b, g, hc, hf, hcomp⟩ := exists_finite_relative_boundary_cover K hK A Q
  exact exists_replacement_stage_of_boundary_cover K A Q N b g hc hf hcomp

end AlgebraicGeometry.FiniteSplitEtaleHypercover
