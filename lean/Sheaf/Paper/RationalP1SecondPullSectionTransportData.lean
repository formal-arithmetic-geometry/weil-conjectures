/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PullSectionTransport
public import Sheaf.Paper.RationalP1SecondPullComparison
public import Sheaf.Paper.ProjectiveDiagonalPullback

/-! The concrete tensor/shift transport data for the rational projective-line square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line twist firstProjection secondProjection square
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward

/-- The native tensor and shift comparisons commute with restriction to the diagonal.
The fields are exactly the two section naturality equations and the square comparison
naturality equation needed by `pull_section_transport`.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md,
Second identity, tensor comparison and shift coherence.
(blueprint: lem-sfb-rational-p1-second-pull-section-transport-data).
Proof: use the unrestricted delta and composition comparison clauses for the module-ringed
topos equivalence. On K-flat representatives the pullback tensor comparison sends pure
tensors to pure tensors and the canonical shift comparison is natural. The equations
then descend to the unbounded derived category and are preserved by the fixed Tate-line
comparison. The same argument applies to finite and closure coefficient indices. -/
theorem second_pull_section_transport_data
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [hproj : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [hdiag : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    ∃ data : PullSectionTransportData
      (F₁ := moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y))
      (F₂ := moduleObjectDerivedPullback (coefficient l c).X (secondProjection Y))
      (G := moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y))
      (s₁ := pullSectionIso (coefficient l c).X Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _))
      (s₂ := pullSectionIso (coefficient l c).X Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _))
      (T := twist (coefficient l c).X (ProjectiveLine Y)
        (line l c (ProjectiveLine Y)))
      (U := twist (coefficient l c).X (diagonalSurface Y)
        (line l c (diagonalSurface Y)))
      (M := ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))
      (e₁ := pullTwistIso (coefficient l c).X (firstProjection Y) _ _
        (shiftedLineComparison l c (firstProjection Y))
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))
      (e₂ := pullTwistIso (coefficient l c).X (secondProjection Y) _ _
        (secondLineComparison l c k p hpl Y)
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))
      (b := (ambientPullbackComparison (coefficient l c).X (square Y)).symm.app K), True := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
