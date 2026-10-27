/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CanonicalSectionProjectionCore

/-! # Supported-unit transport for section/projection coherence -/

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
attribute [local irreducible] projectionMap singleUnitIso
attribute [local irreducible] pullSectionIso supportedUnitIso pushSectionIso

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The supported-unit transport equality for section/projection coherence.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md,
second identity, coefficient normalization after the section identity.
(blueprint: lem-sfb-projective-canonical-section-projection-transport).

Proof: use naturality of the canonical projection map in its coefficient argument for the
supported-unit isomorphism, then cancel the inverse/hom pair under the direct image. The
result identifies the normalized expression with the regular-coefficient expression;
the core section/projection identity is applied separately by the parent theorem.
-/
theorem canonical_section_projection_transport
    (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (ρ_ M).inv ≫
      (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫
        (pushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)) ≫
        (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
          (supportedUnitIso Λ Y).hom)) ≫
      projectionMap Λ (secondProjection Y) M
        ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
          (source Λ Y)) ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        ((((moduleObjectDerivedPullback Λ (secondProjection Y)).obj M) ◁
          (supportedUnitIso Λ Y).inv) ≫
          sectionTensorMap Λ (diagonalImmersion Y) (secondProjection Y)
            (pullSectionIso Λ Y (secondProjection Y)
              (by unfold secondProjection; exact pullback.diagonal_snd _))
            (unit Λ (ProjectiveLine Y)) (singleUnitIso Λ (ProjectiveLine Y)) M) =
    (ρ_ M).inv ≫
      (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫
        (pushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)))) ≫
      projectionMap Λ (secondProjection Y) M
        ((moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj
          (unit Λ (ProjectiveLine Y))) ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        (sectionTensorMap Λ (diagonalImmersion Y) (secondProjection Y)
          (pullSectionIso Λ Y (secondProjection Y)
            (by unfold secondProjection; exact pullback.diagonal_snd _))
          (unit Λ (ProjectiveLine Y)) (singleUnitIso Λ (ProjectiveLine Y)) M) := by
  sorry


end AlgebraicGeometry.ProEtale.RationalP1
