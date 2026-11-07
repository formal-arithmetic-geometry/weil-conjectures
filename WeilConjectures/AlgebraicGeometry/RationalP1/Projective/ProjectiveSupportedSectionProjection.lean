/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveCanonicalSectionProjection
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveSupportedSourceNormalization

/-! # Projection coherence on the supported diagonal source -/

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
attribute [local irreducible] projectionMap singleUnitIso secondLineComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

-- The statement compares the fixed derived pullback and tensor interfaces.
/-- Section/projection coherence on the supported coefficient source, before any class map.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md,
Second identity, the section identity Rp2* RDelta* = id; Stacks Tags 0B56 and 0DV0.
(blueprint: lem-sfb-projective-supported-section-projection).

Proof: specialize the section identity in ringedProjectionTensorComposition to the
closed section Delta of p2 and transport it by the normalized internal-module/ringed
comparison. Use the unrestricted projection_comparison, derived_homEquiv and
composition_comparison clauses of ModuleRingedComparison: its finite-type wrapper
theorem is not needed. Its two projection arrows are the fixed projectionMap arrows, and the
right comparison is conjugate to pullSectionIso, hence is pushSectionIso. Specialize
the coefficient argument to the regular module and compose with its right unitor.
This gives the identity using pushSectionIso on the regular coefficient source.
The exact closed direct image identifies this source with supportedUnitIso.
On single complexes, the normalization of d.support2.iso is precisely the ordinary
composition Delta p2 = id. The full-unit equation d.p2_unit identifies its subsequent
right-derived source arrow with the canonical right-derived unit. Thus the coefficient
source arrow is d.support2.hom followed by secondDiagramPushIso. Substitute this in
the section identity to obtain the displayed formula. Only the supported source and
its normalization are used from d: no delta, trace or integration equation occurs.
This proof applies to arbitrary unbounded M, including zero M and empty Y. -/
theorem supported_section_projection
    (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (ρ_ M).inv ≫
      (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫ d.support₂.hom ≫
        (secondDiagramPushIso Λ Y L d).hom.app
          ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
            (source Λ Y)))) ≫
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
  rw [supported_source_normalization Λ Y L d M]
  exact canonical_section_projection Λ Y M

end AlgebraicGeometry.ProEtale.RationalP1
