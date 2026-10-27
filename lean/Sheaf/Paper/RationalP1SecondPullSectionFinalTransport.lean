/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RationalP1SecondPullSectionTransportSpecialized
public import Sheaf.Paper.RationalP1SecondPullComparisonExpansion
public import Sheaf.Paper.ProjectivePullSectionCompatibility

/-! Final assembly of the restricted comparison from transport data. -/

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

attribute [local irreducible] coefficient line twist firstProjection secondProjection
attribute [local irreducible] square pullSectionIso
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward

/-- The final assembly uses the already isolated transport data and comparison
expansion; the remaining categorical coherence is the stated intermediate step.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
(blueprint: lem-sfb-rational-p1-second-pull-section-final-assembly).
-/
theorem second_pull_section_final_assembly
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y))
    :
    (moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y)).map
        (secondPullComparison l c k p hpl Y K).inv ≫
      (pullSectionIso (coefficient l c).X Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _)).hom.app
        ((twist (coefficient l c).X (ProjectiveLine Y)
          (line l c (ProjectiveLine Y))).obj
          ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K)) =
      (pullSectionIso (coefficient l c).X Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _)).hom.app
        ((twist (coefficient l c).X (ProjectiveLine Y)
          (line l c (ProjectiveLine Y))).obj
          ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
