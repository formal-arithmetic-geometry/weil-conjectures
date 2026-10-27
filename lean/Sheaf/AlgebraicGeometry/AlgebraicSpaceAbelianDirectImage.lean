/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Representable
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests

/-! # Representable base change and abelian direct image

Source: Stacks Project, Properties of Spaces, Tags 03G2(4) and 03LR
(blueprint: def-sfb-space-representable-abelian-direct-image).

The universal property of each scheme fibre product fixes base change and its
projections up to unique compatible isomorphism. Direct image is precomposition
with this base-change functor, including its actual action on sections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S}

/-- Forget a chart's map to the algebraic space, retaining its scheme over `S`.
Source: Stacks, Tag 03G2(4)
(blueprint: def-sfb-space-representable-abelian-direct-image). -/
def etaleOverForget (X : AlgebraicSpace S) : X.EtaleSite ⥤ Over S :=
  ObjectProperty.ι _ ⋙ CostructuredArrow.proj yoneda X.obj.obj

/-- Base change with its representing pullback squares and natural scheme projections.
The squares determine objects and arrows up to unique isomorphism compatible with both
projections. Continuity is a property of that fixed functor, not additional map data.
Source: Stacks, Tags 03G2(4) and 03LR
(blueprint: def-sfb-space-representable-abelian-direct-image). -/
structure RepresentableEtaleBaseChange (i : Z ⟶ X) where
  /-- `U ↦ U ×_X Z`. -/
  functor : X.EtaleSite ⥤ Z.EtaleSite
  /-- Scheme projection `U ×_X Z → U`. -/
  projection : functor ⋙ etaleOverForget Z ⟶ etaleOverForget X
  /-- The scheme chart really represents the fibre product. -/
  square (U : X.EtaleSite) :
    IsPullback (functor.obj U).obj.hom (yoneda.map (projection.app U))
      i.hom.hom U.obj.hom
  /-- Base change preserves the covering equalizers. -/
  continuous : functor.IsContinuous X.etaleTopology Z.etaleTopology

/-- Representability supplies the continuous base-change functor with its fibre-product
universal property, so its choice determines no arbitrary unnormalized map.
Source: Stacks, Tags 03G2(4) and 03LR
(blueprint: def-sfb-space-representable-abelian-direct-image).
Proof: for every étale scheme `U → X`, represent `U ×_X Z` by a scheme using the
representability hypothesis. Its projection to `Z` is étale by base change of `U → X`.
For every chart arrow use the unique morphism of the two representing pullback squares.
Uniqueness gives identity, composition and naturality of the projections. Coverings remain
jointly surjective étale coverings after base change; their covering pullback squares
remain pullbacks by pasting. The generating-cover criterion therefore gives continuity.
The universal property determines these choices up to unique projection-compatible iso. -/
theorem representableEtaleBaseChange_nonempty (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom.hom) :
    Nonempty (RepresentableEtaleBaseChange i) := by
  sorry

/-- The universal-property choice of the actual scheme base-change functor.
Source: Stacks, Tag 03G2(4)
(blueprint: def-sfb-space-representable-abelian-direct-image). -/
def representableEtaleBaseChange (i : Z ⟶ X) (hi : yoneda.relativelyRepresentable i.hom.hom) :
    RepresentableEtaleBaseChange i :=
  Classical.choice (representableEtaleBaseChange_nonempty i hi)

/-- Abelian direct image is precomposition with scheme base change, so its value at
`U` is exactly the section group on the representing scheme `U ×_X Z`.
Source: Stacks, Tags 03G2(4) and 03LR
(blueprint: def-sfb-space-representable-abelian-direct-image). -/
def representableAbelianDirectImage (i : Z ⟶ X) (hi : yoneda.relativelyRepresentable i.hom.hom) :
    Sheaf Z.etaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf X.etaleTopology AddCommGrpCat.{u + 1} :=
  letI := (representableEtaleBaseChange i hi).continuous
  (representableEtaleBaseChange i hi).functor.sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} X.etaleTopology Z.etaleTopology

end AlgebraicGeometry.AlgebraicSpace
