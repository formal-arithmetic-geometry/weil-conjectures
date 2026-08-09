/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.GuitartExact.KanExtension

/-!
# Guitart exact squares and right Kan extensions

Given a Guitart exact square `w : T ⋙ R ⟶ L ⋙ B`,
```
     T
  C₁ ⥤ C₂
L |     | R
  v     v
  C₃ ⥤ C₄
     B
```
we show that an extension `G' : C₄ ⥤ D` of `G : C₃ ⥤ D` along `B`
is a pointwise right Kan extension at `R.obj X₂` iff `R ⋙ G'` is
a pointwise right Kan extension of `L ⋙ G` along `T` at `X₂`.

This file is obtained by dualizing `Mathlib/CategoryTheory/GuitartExact/KanExtension.lean`;
the two files should be kept in sync. Note that the duality is the one which exchanges
the two "directions" of the square (`T`/`B` and `L`/`R`), so that the Guitart exactness
of `w` is used through the initiality of the functors `w.structuredArrowDownwards X₂`,
rather than the finality of the functors `w.costructuredArrowRightwards X₃`.

In mathlib, this file would be part of
`Mathlib/CategoryTheory/GuitartExact/KanExtension.lean`.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

open Limits

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} {D : Type u₅}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  [Category.{v₅} D]

namespace Functor.RightExtension

variable {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
  {G : C₃ ⥤ D} (E : B.RightExtension G)

/-- Given a square `w : TwoSquare T L R B` (consisting of a natural transformation
`T ⋙ R ⟶ L ⋙ B`), this is the obvious map `B.RightExtension G → T.RightExtension (L ⋙ G)`
obtained by the precomposition with `R` and the postcomposition with `w`. -/
abbrev compTwoSquare (w : TwoSquare T L R B) : T.RightExtension (L ⋙ G) :=
  RightExtension.mk (R ⋙ E.left)
    ((associator _ _ _).inv ≫ whiskerRight w.natTrans _ ≫
      (associator _ _ _).hom ≫ whiskerLeft _ E.hom)

set_option backward.defeqAttrib.useBackward true in
/-- If `w : TwoSquare T L R B` is a Guitart exact square, and `E` is a right extension
of `G` along `B`, then `E` is a pointwise right Kan extension of `G` along `B` at
`R.obj X₂` iff `E.compTwoSquare w` is a pointwise right Kan extension
of `L ⋙ G` along `T` at `X₂`. -/
noncomputable def isPointwiseRightKanExtensionAtCompTwoSquareEquiv
    (w : TwoSquare T L R B) (X₂ : C₂) [Initial (w.structuredArrowDownwards X₂)] :
    (E.compTwoSquare w).IsPointwiseRightKanExtensionAt X₂ ≃
      E.IsPointwiseRightKanExtensionAt (R.obj X₂) := by
  refine Equiv.trans ?_ (Initial.isLimitWhiskerEquiv (w.structuredArrowDownwards X₂) _)
  exact IsLimit.equivIsoLimit (Cone.ext (Iso.refl _))

lemma nonempty_isPointwiseRightKanExtensionAt_compTwoSquare_iff
    (w : TwoSquare T L R B) (X₂ : C₂) [Initial (w.structuredArrowDownwards X₂)] :
    Nonempty ((E.compTwoSquare w).IsPointwiseRightKanExtensionAt X₂) ↔
      Nonempty (E.IsPointwiseRightKanExtensionAt (R.obj X₂)) :=
  (E.isPointwiseRightKanExtensionAtCompTwoSquareEquiv w _).nonempty_congr

variable {E} in
/-- If `w : TwoSquare T L R B` is a Guitart exact square, and `E` is a pointwise
right Kan extension of `G` along `B`, then `E.compTwoSquare w` is a pointwise right
Kan extension of `L ⋙ G` along `T`. -/
noncomputable def IsPointwiseRightKanExtension.compTwoSquare
    (h : E.IsPointwiseRightKanExtension) (w : TwoSquare T L R B) [w.GuitartExact] :
    (E.compTwoSquare w).IsPointwiseRightKanExtension :=
  fun X₂ ↦ (E.isPointwiseRightKanExtensionAtCompTwoSquareEquiv w X₂).symm (h _)

end Functor.RightExtension

namespace TwoSquare

variable {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
  (w : TwoSquare T L R B)

include w in
lemma hasPointwiseRightKanExtensionAt_iff
    (G : C₃ ⥤ D) (X₂ : C₂) [(w.structuredArrowDownwards X₂).Initial] :
    T.HasPointwiseRightKanExtensionAt (L ⋙ G) X₂ ↔
      B.HasPointwiseRightKanExtensionAt G (R.obj X₂) := by
  dsimp [Functor.HasPointwiseRightKanExtensionAt]
  rw [← Functor.Initial.hasLimit_comp_iff (w.structuredArrowDownwards X₂)]
  rfl

end TwoSquare

end CategoryTheory
