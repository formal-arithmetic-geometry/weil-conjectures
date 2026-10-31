/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1DiagonalTensor
import WeilConjectures.AlgebraicGeometry.RationalP1.Canonical.CanonicalSectionProjectionTransport

/-! # Canonical section/projection identity on the supported diagonal source -/

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
attribute [local irreducible] supportedUnitIso pushSectionIso

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical section/projection identity for the regular supported source.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md,
Second identity, cancellation on the diagonal before coefficient normalization.
(blueprint: lem-sfb-projective-canonical-section-projection).

Proof: specialize the section clause of ringed projection/composition coherence to the
closed diagonal and the second projection, transport through the fixed internal-module
comparison, and evaluate it on the regular coefficient. The conjugate comparison is
pushSectionIso, the exact closed direct image is supportedUnitIso, and the two unitors
are singleUnitIso and the right unitor. The result is the displayed equality for every
unbounded M, including zero and empty schemes. -/
theorem canonical_section_projection
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
      (pushSectionIso Λ Y).hom.app M := by
  rw [canonical_section_projection_transport Λ Y M]
  exact canonical_section_projection_core Λ Y M

end AlgebraicGeometry.ProEtale.RationalP1
