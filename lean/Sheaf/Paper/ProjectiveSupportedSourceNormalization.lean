/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B9
-/
module

public import Sheaf.Paper.RationalP1SecondPullComparison

/-! # Normalization of the supported coefficient source -/

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

attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] projectionMap singleUnitIso

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The normalized diagram source arrow is the canonical supported-unit arrow.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md,
Second identity, source normalization after the full second derived unit.
(blueprint: lem-sfb-projective-supported-source-normalization).

Proof: unfold secondDiagramPushIso and use the canonical right-derived unit equation
`d.p₂_unit` on the single regular module. The SupportNormalization field of
`d.support₂` identifies its ordinary source isomorphism with the closed-section
composition, which is exactly supportedUnitIso after passage to the fixed derived
module interface. Naturality of the comparison then gives the displayed equality.
No delta, trace, integration, or twist data is used. -/
theorem supported_source_normalization
    (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫ d.support₂.hom ≫
      (secondDiagramPushIso Λ Y L d).hom.app
        ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
          (source Λ Y)))) =
    (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫
      (pushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)) ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        (supportedUnitIso Λ Y).hom)) := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
