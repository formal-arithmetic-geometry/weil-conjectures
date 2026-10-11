/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Isomorphisms of arrows from factorisations

An arrow `a ≫ c ≫ b` with `a` and `b` isomorphisms is isomorphic to `c`
(`CategoryTheory.Arrow.isoOfIsIsoComp`), and an isomorphism `x ≅ y` identifies the arrows
`H (α_x)` and `H (α_y)` attached to a natural transformation `α` and a functor `H`
(`CategoryTheory.Arrow.isoMapApp`). These are the forms in which a morphism is identified with
another one, up to isomorphism, once a factorisation of it is known.
-/

@[expose] public section

namespace CategoryTheory.Arrow

variable {C : Type*} [Category* C]

/-- An arrow `a ≫ c ≫ b` with `a` and `b` isomorphisms is isomorphic to `c`. -/
@[simps!]
noncomputable def isoOfIsIsoComp {W X Y Z : C} (a : W ⟶ X) [IsIso a] (c : X ⟶ Y)
    (b : Y ⟶ Z) [IsIso b] : Arrow.mk (a ≫ c ≫ b) ≅ Arrow.mk c :=
  Arrow.isoMk (asIso a) (asIso b).symm (by simp)

/-- An isomorphism `x ≅ y` identifies the arrows `H (α_x)` and `H (α_y)`, for a natural
transformation `α : P ⟶ Q` and a functor `H`. -/
@[simps!]
def isoMapApp {D E : Type*} [Category* D] [Category* E] {P Q : C ⥤ D} (α : P ⟶ Q)
    (H : D ⥤ E) {x y : C} (ι : x ≅ y) :
    Arrow.mk (H.map (α.app x)) ≅ Arrow.mk (H.map (α.app y)) :=
  Arrow.isoMk (H.mapIso (P.mapIso ι)) (H.mapIso (Q.mapIso ι)) (by
    simp only [Arrow.mk_left, Arrow.mk_right, Functor.mapIso_hom, Arrow.mk_hom, ← H.map_comp,
      α.naturality])

/-- The component of a whiskered natural transformation `E ◁ (α ▷ H)` at `x` is, as an arrow,
`H (α_{E x})`. Stated for abstract functors, this identification is checked syntactically
when the functors are instantiated. -/
lemma mk_whiskerLeft_whiskerRight_app {B D E : Type*} [Category* B] [Category* D]
    [Category* E] (F : B ⥤ C) {P Q : C ⥤ D} (α : P ⟶ Q) (H : D ⥤ E) (x : B) :
    Arrow.mk ((Functor.whiskerLeft F (Functor.whiskerRight α H)).app x) =
      Arrow.mk (H.map (α.app (F.obj x))) :=
  rfl

end CategoryTheory.Arrow
