/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Postcomposing a transformation of bifunctors

Given a natural transformation `τ : (postcompose₂.obj F).obj G ⟶ (whiskeringLeft₂ F₁ F₂).obj B`
of bifunctors and a functor `Q`, we define the natural transformation
`(postcompose₂.obj (F ⋙ Q)).obj G ⟶ (whiskeringLeft₂ F₁ F₂).obj ((postcompose₂.obj Q).obj B)`
obtained by postcomposing with `Q`. It is definitionally `(postcompose₂.obj Q).map τ`; having it
as a separate definition, whose type mentions `F ⋙ Q`, avoids expensive definitional unfoldings
when `F` and `Q` are concrete functors.

-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C₁ C₂ D₁ D₂ E E' E'' : Type*} [Category* C₁] [Category* C₂] [Category* D₁]
  [Category* D₂] [Category* E] [Category* E'] [Category* E'']

/-- The postcomposition of a natural transformation
`τ : (postcompose₂.obj F).obj G ⟶ (whiskeringLeft₂ F₁ F₂).obj B` of bifunctors with a functor
`Q`, as a natural transformation
`(postcompose₂.obj (F ⋙ Q)).obj G ⟶ (whiskeringLeft₂ F₁ F₂).obj ((postcompose₂.obj Q).obj B)`. -/
@[simps!]
def postcompose₂CompMap {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂} {G : C₁ ⥤ C₂ ⥤ E} {F : E ⥤ E'}
    {B : D₁ ⥤ D₂ ⥤ E'}
    (τ : (postcompose₂.obj F).obj G ⟶ (((whiskeringLeft₂ E').obj F₁).obj F₂).obj B)
    (Q : E' ⥤ E'') :
    (postcompose₂.obj (F ⋙ Q)).obj G ⟶
      (((whiskeringLeft₂ E'').obj F₁).obj F₂).obj ((postcompose₂.obj Q).obj B) :=
  (postcompose₂.obj Q).map τ

instance {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂} {G : C₁ ⥤ C₂ ⥤ E} {F : E ⥤ E'}
    {B : D₁ ⥤ D₂ ⥤ E'}
    (τ : (postcompose₂.obj F).obj G ⟶ (((whiskeringLeft₂ E').obj F₁).obj F₂).obj B)
    [IsIso τ] (Q : E' ⥤ E'') :
    IsIso (postcompose₂CompMap τ Q) :=
  inferInstanceAs (IsIso ((postcompose₂.obj Q).map τ))

end CategoryTheory.Functor
