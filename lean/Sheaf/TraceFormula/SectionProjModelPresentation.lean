/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.TraceFormula.SectionProjModel

/-! # Presenting section algebras on affine opens

Source: Stacks Project, Tags 0D3C, 0D2Z and 01O9
(blueprint: lem-trf-section-proj-model-presentation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Every normalized section algebra has an affine graded presentation, retaining the
specified homogeneous sheaves and all their evaluations.

Source: Stacks, Constructions, Tag 01LH; Descent on Spaces, Tag 0D3C, the section algebra
and maps psi_d (blueprint: lem-trf-section-proj-model-presentation).

Proof: regard A.total, A.degree and A.graded as a RelativeProjAlgebra. Its decomposition
is the unique comparison of the coproduct cocone with A.sum; the inclusion equations
are the comparison's projection equations. On an affine open, sections of this coproduct
are the direct sum of the sections of the quasi-coherent degrees. Each inclusion is
injective, so it identifies its homogeneous module with its image in the total section
ring. Give that ring this internal grading. Restriction is the ordinary restriction of
the total algebra; affine quasi-coherent base change gives graded scalar extension.
These are GradedAlgebraData. The image identifications are degreeIso. The given sum_mul,
sum_unit and naturality of inclusions give its product, unit and restriction equations.
Define the homogeneous evaluation by applying A.image to the inverse degreeIso. The
adjunction unit is additive and semilinear, so this defines the additive components and
scalar equation. A.mul and A.unit give the graded-map equations. A.naturality gives
naturality on tests, and naturality of tensor-pullback sections gives affine restriction.
The inverse laws of degreeIso give evaluation_eq. Nothing is chosen from an existence
of an unspecified graded algebra: the rings are the actual total section rings. Empty
opens give zero rings, and degree zero retains the full base-algebra structure map. -/
theorem section_proj_model_presentation {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    {f : F ⟶ yoneda.obj T} {L : TestLineFamily F} (A : SpaceSectionAlgebra f L) :
    ∃ M : SectionProjModel f L, M.sections = A := by sorry

end AlgebraicGeometry.AlgebraicSpace
