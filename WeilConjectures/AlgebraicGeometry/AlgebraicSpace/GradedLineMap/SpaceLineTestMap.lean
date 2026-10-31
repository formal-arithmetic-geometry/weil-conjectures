/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace.SpaceLineModuleProjInput

/-! # The canonical relative-Proj morphism on one generating scheme test

Source: Stacks Project, Constructions, Tags 01NK and 01O9
(blueprint: lem-trf-space-line-test-map).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The scheme morphism is specified after every further scheme test by the usual
trivialized homogeneous-section formula. Source: Stacks, Tags 01NK and 01O9
(blueprint: lem-trf-space-line-test-map). -/
def GradedLineMap.IsCanonicalTestMap {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S} {f : F ⟶ yoneda.obj T}
    {A : T.left.GradedAlgebraData} {L : TestLineFamily F}
    (ψ : GradedLineMap f A L) (W : SchemeTests F)
    (q : W.left ⟶ projOver T A) : Prop :=
  q.left ≫ A.relProjHom = (testToBase f W).left ∧
    ∀ (V : SchemeTests F) (j : V ⟶ W) (C : T.left.affineOpens)
      (h : (⊤ : V.left.left.Opens) ≤ (testToBase f V).left ⁻¹ᵁ C.1)
      (e : L.module V ≅ SheafOfModules.unit V.left.left.ringCatSheaf)
      (α : A.obj C →+* Γ(V.left.left, ⊤)),
      (∀ (n : ℕ) (b : A.grading C n), α b =
        (Scheme.Modules.unitSectionsEquiv ⊤).symm
          ((trivializedPower e n).hom.app ⊤ (ψ.component V C h n b))) →
      ∀ hα : Ideal.map α (HomogeneousIdeal.irrelevant (A.grading C)).toIdeal = ⊤,
        j.left.left ≫ q.left =
          Proj.fromOfGlobalSections (A.grading C) α hα ≫ A.relProjι C

/-- The scheme construction of the fraction morphism, before assembling any map of
presheaves or asserting any base-change formula. It applies to one generating test
of an arbitrary coherent cartesian family.

Source: Stacks Project, Constructions, Tags 01NK and 01O9, construction, uniqueness
and restriction compatibility (blueprint: lem-trf-space-line-test-map).

Proof: Cover the test scheme by affine opens above affine opens of the base, with a
frame of its invertible module. Transport homogeneous images to scalars in this
frame. The unit and product equations and the direct-sum decomposition extend these
to a ring homomorphism. Generation at each point makes the image of the irrelevant
ideal the unit ideal locally. On each such open apply Proj.fromOfGlobalSections and
then the affine-base embedding into relative Proj. Changing the frame multiplies a
degree-n scalar by the n-th power of a unit; the homogeneous fractions are unchanged.
Restrictions of coefficients agree by the restriction equation of the graded map.
On overlaps refine the two affine base opens by affine opens and use those same
fraction formulas; this does not assume the overlap is affine. Glue the morphisms.
The degree-zero scalar equation makes the result a morphism over the base. For an
arbitrary further scheme test, cartesian coherence identifies the powers of its
pulled-back line with the specified powers. Naturality of the components then gives
the same fraction maps on the inverse images of the cover. Thus the glued map has
the stated formula on every such test. Conversely the formula on trivializing affine
opens fixes a morphism, since their positive-degree generator opens cover the test.
The empty scheme uses the empty cover. Neither finite generation nor degree-one
generation nor equality of the degree-zero algebra with the structure sheaf is used. -/
theorem existsUnique_space_line_test_map {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S} {f : F ⟶ yoneda.obj T}
    {A : T.left.GradedAlgebraData} {L : TestLineFamily F}
    (hL : L.IsCoherent) (ψ : GradedLineMap f A L)
    (W : SchemeTests F) (hW : ψ.generationSet W = Set.univ) :
    ∃! q : W.left ⟶ projOver T A, ψ.IsCanonicalTestMap W q := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
