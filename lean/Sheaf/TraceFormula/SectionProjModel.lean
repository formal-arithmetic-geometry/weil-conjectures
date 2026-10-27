/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.TraceFormula.SpaceSectionAlgebraEtaleBaseChange

/-! # Affine presentations of the canonical graded section algebra

Source: Stacks Project, Tags 0D3C, 01LH and 0D2Z
(blueprint: def-trf-section-proj-model).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A section algebra and its equivalent affine presentation for the existing Proj API.
The linear equivalences identify all homogeneous sections, their products, units and
restrictions. Since an affine graded algebra is the direct sum of its homogeneous
pieces, these specify the whole graded algebra, including its degree-zero structure
map. The evaluation equation fixes the map on every homogeneous section and hence on
every tensor generator with arbitrary local scalar coefficient.

This is an adapter for the two recorded dependency interfaces, not additional data
assumed about the geometric objects. Source: Stacks, Tags 0D3C, 01LH and 0D2Z
(blueprint: def-trf-section-proj-model). -/
structure SectionProjModel {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (f : F ⟶ yoneda.obj T) (L : TestLineFamily F) where
  sections : SpaceSectionAlgebra f L
  affine : T.left.GradedAlgebraData
  degreeIso (V : T.left.affineOpens) (n : ℕ) :
    Γ(sections.degree n, V.1) ≃ₗ[Γ(T.left, V.1)] affine.grading V n
  mul (V : T.left.affineOpens) (m n : ℕ)
      (a : Γ(sections.degree m, V.1)) (b : Γ(sections.degree n, V.1)) :
    (degreeIso V (m + n) (sections.graded.mul m n V.1 a b) : affine.obj V) =
      (degreeIso V m a : affine.obj V) * (degreeIso V n b : affine.obj V)
  unit (V : T.left.affineOpens) (r : Γ(T.left, V.1)) :
    (degreeIso V 0 (sections.graded.unit.val.app (op V.1) r) : affine.obj V) =
      algebraMap Γ(T.left, V.1) (affine.obj V) r
  restriction (V V' : T.left.affineOpens) (j : V ≤ V') (n : ℕ)
      (a : Γ(sections.degree n, V'.1)) :
    (degreeIso V n ((sections.degree n).val.map (homOfLE j).op a) : affine.obj V) =
      affine.res j (degreeIso V' n a)
  evaluation : GradedLineMap f affine L
  evaluation_eq (W : SchemeTests F) (V : T.left.affineOpens)
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V.1)
      (n : ℕ) (a : Γ(sections.degree n, V.1)) :
    evaluation.component W V h n (degreeIso V n a) = sections.image V.1 W h n a

end AlgebraicGeometry.AlgebraicSpace
