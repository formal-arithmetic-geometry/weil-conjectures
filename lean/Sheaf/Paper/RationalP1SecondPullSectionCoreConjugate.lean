/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RationalP1SecondPullComparison
public import Sheaf.Paper.ProjectivePullSectionCompatibility
public import Sheaf.Paper.ProjectiveDiagonalPullback

/-! Conjugated form of the untwisted diagonal restriction. -/

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

/--
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md,
Second identity, first factor before the Tate twist.
(blueprint: lem-sfb-rational-p1-second-pull-section-core-conjugate).
Proof: expand the ambient square comparison into the normalized inverse-image compositors.
Restrict along the diagonal, use both diagonal projection identities, and cancel the
identity compositor. The resulting conjugated comparison is the map below.
-/
theorem second_pull_section_core_conjugate
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    (moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y)).map
        ((ambientPullbackComparison (coefficient l c).X (square Y)).symm.app K).inv =
      (pullSectionIso (coefficient l c).X Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _)).hom.app
        ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K) ≫
      (pullSectionIso (coefficient l c).X Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _)).inv.app
        ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K) := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
