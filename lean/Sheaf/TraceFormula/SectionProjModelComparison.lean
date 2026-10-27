/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.TraceFormula.SectionProjModel

/-! # Transporting normalized section-algebra base change

Source: Stacks Project, Tags 0D3C, 0D2Z and 01O9
(blueprint: lem-trf-section-proj-model-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A normalized section-algebra comparison induces the coefficientwise affine graded
comparison to any presentation of the same local section algebra.

Source: Stacks, Properties of Spaces, Tag 03LX and Constructions, Tag 01LH; the restriction
and evaluation sentence in the proof of Tag 0D3C
(blueprint: lem-trf-section-proj-model-comparison).

Proof: for each base open and degree, the sections universal properties of B and
M'.sections represent the same compatible families of sections on the same tests.
Their unique comparison is additive, linear, commutes with restriction, and intertwines
evaluation. Its inverse is obtained by interchanging the two universal properties.
The product and unit equations follow by evaluation on every test and uniqueness in
sections. Summing these degree isomorphisms gives the total module isomorphism and
respects the inclusions. Transport beta along these isomorphisms to obtain beta'.
Compose tensor-pullback sections, beta'.degree and the two degreeIso maps; on affine
opens this is the coefficient map. Extend the homogeneous maps to their direct sums.
The product and unit equations make this a graded algebra homomorphism. Naturality
makes these maps commute with affine restrictions. Affine sections of quasi-coherent
tensor pullbacks give the required graded base-change property, hence PullbackData D.
This construction is precisely the displayed degree equation. Evaluate on a test:
beta.evaluation and the two evaluation_eq equations identify both paths with the same
restricted section, which is IsBaseChange. Finally transport the ordinary-scheme
comparison of B along the degree isomorphisms; the evaluation normalization gives the
counit equation for M'.sections. This works in degree zero and over empty schemes. -/
theorem section_proj_model_comparison
    {F F' : (Over S)ᵒᵖ ⥤ Type u} {T T' : Over S}
    {f : F ⟶ yoneda.obj T} {f' : F' ⟶ yoneda.obj T'} {L : TestLineFamily F}
    (k : F' ⟶ F) (g : T' ⟶ T)
    (hcomm : k ≫ f = f' ≫ yoneda.map g)
    (M : SectionProjModel f L) (M' : SectionProjModel f' (L.pullback k))
    (B : SpaceSectionAlgebra f' (L.pullback k))
    (beta : SpaceSectionAlgebraBaseChange k g M.sections B) (hB : B.AgreesWithSchemes) :
    M'.sections.AgreesWithSchemes ∧
      ∃ (β : SpaceSectionAlgebraBaseChange k g M.sections M'.sections)
        (D : Scheme.GradedAlgebraData.PullbackData g.left M.affine M'.affine),
        (∀ (V : T.left.affineOpens) (V' : T'.left.affineOpens)
          (h : V'.1 ≤ g.left ⁻¹ᵁ V.1) (n : ℕ) (s : Γ(M.sections.degree n, V.1)),
          D.map h (M.degreeIso V n s) =
            (M'.degreeIso V' n ((β.degree n).hom.app V'.1
              (sectionAlgebraPullSection g.left (M.sections.degree n)
                V.1 V'.1 h s)) : M'.affine.obj V')) ∧
        M.evaluation.IsBaseChange k g D M'.evaluation := by sorry

end AlgebraicGeometry.AlgebraicSpace
