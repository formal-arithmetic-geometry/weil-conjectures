/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RationalP1DiagonalTensor

/-! # Categorical cancellation step for the canonical section projection -/

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
attribute [local irreducible] supportedUnitIso pushSectionIso

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/--
The categorical cancellation form of the section/projection coherence identity.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md,
second identity before coefficient normalization.
(blueprint: lem-sfb-projective-canonical-section-projection-core-coherence).

Proof: apply the section case of the ringed projection/composition coherence to the
closed diagonal and the second projection.  Transport the resulting identity through
the fixed internal-module comparison, evaluate it on the regular coefficient, and
postcompose by the inverse of the canonical pushforward comparison.  The remaining
right-unitor and pullback-section factors are exactly those displayed in the theorem.
-/
theorem canonical_section_projection_core_coherence
    (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    ((ρ_ M).inv ≫
      (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫
        (pushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)))) ≫
      projectionMap Λ (secondProjection Y) M
        ((moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj
          (unit Λ (ProjectiveLine Y))) ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        (sectionTensorMap Λ (diagonalImmersion Y) (secondProjection Y)
          (pullSectionIso Λ Y (secondProjection Y)
            (by unfold secondProjection; exact pullback.diagonal_snd _))
          (unit Λ (ProjectiveLine Y)) (singleUnitIso Λ (ProjectiveLine Y)) M)) ≫
      (pushSectionIso Λ Y).inv.app M = 𝟙 _ := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
