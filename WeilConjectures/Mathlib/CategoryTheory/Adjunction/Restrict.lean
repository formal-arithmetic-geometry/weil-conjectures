/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Restricting an adjunction to full subcategories

An adjunction `L ⊣ R` restricts to full subcategories `P` and `Q` preserved by `L` and `R`, with
the same unit and counit
(`CategoryTheory.ObjectProperty.liftFullSubcategoryAdjunction`).

## Left adjoints commuting with fully faithful functors

Let `iC : C ⥤ C'` and `iD : D ⥤ D'` be fully faithful, and let `L' ⊣ R'` and `L ⊣ R` be
adjunctions `C' ⇄ D'` and `C ⇄ D` such that `iD ⋙ R' ≅ R ⋙ iC`. If `L'` maps the image of `iC`
into the essential image of `iD`, then `iC ⋙ L' ≅ L ⋙ iD`: lifting `iC ⋙ L'` along `iD` gives a
functor `C ⥤ D` which is left adjoint to `R` by `CategoryTheory.Adjunction.restrictFullyFaithful`,
hence isomorphic to `L`.

The left adjoints are then isomorphic: `CategoryTheory.Adjunction.compIsoOfForallMemEssImage`.
-/

@[expose] public section

universe v v' u u'

open CategoryTheory

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {P : ObjectProperty C} {Q : ObjectProperty D} {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (hL : ∀ X, P X → Q (L.obj X)) (hR : ∀ Y, Q Y → P (R.obj Y))

/-- An adjunction `L ⊣ R` restricts to full subcategories `P` and `Q` preserved by `L` and `R`,
with the same unit and counit. -/
def liftFullSubcategoryAdjunction :
    P.liftFullSubcategory Q L hL ⊣ Q.liftFullSubcategory P R hR :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app X := P.homMk (adj.unit.app X.obj)
          naturality _ _ f := P.hom_ext (adj.unit.naturality f.hom) }
      counit :=
        { app Y := Q.homMk (adj.counit.app Y.obj)
          naturality _ _ f := Q.hom_ext (adj.counit.naturality f.hom) }
      left_triangle := NatTrans.ext (funext fun X ↦ Q.hom_ext (by
        simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          Functor.associator_hom_app, FullSubcategory.comp_hom,
          liftFullSubcategory_map, homMk_hom, Category.id_comp]
        exact adj.left_triangle_components X.obj))
      right_triangle := NatTrans.ext (funext fun Y ↦ P.hom_ext (by
        simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          Functor.associator_inv_app, FullSubcategory.comp_hom,
          liftFullSubcategory_map, homMk_hom, Category.id_comp]
        exact adj.right_triangle_components Y.obj)) }

/-- The unit of `liftFullSubcategoryAdjunction` is the unit of `L ⊣ R`. -/
@[simp]
lemma liftFullSubcategoryAdjunction_unit_app_hom (X : P.FullSubcategory) :
    ((liftFullSubcategoryAdjunction adj hL hR).unit.app X).hom = adj.unit.app X.obj :=
  rfl

/-- The counit of `liftFullSubcategoryAdjunction` is the counit of `L ⊣ R`. -/
@[simp]
lemma liftFullSubcategoryAdjunction_counit_app_hom (Y : Q.FullSubcategory) :
    ((liftFullSubcategoryAdjunction adj hL hR).counit.app Y).hom = adj.counit.app Y.obj :=
  rfl

end CategoryTheory.ObjectProperty


namespace CategoryTheory.Adjunction

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
  {iC : C ⥤ C'} {iD : D ⥤ D'} (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful)
  {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj' : L' ⊣ R') {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (comm : iD ⋙ R' ≅ R ⋙ iC) (h : ∀ X, iD.essImage (L'.obj (iC.obj X)))

/-- **Left adjoints commute with fully faithful functors preserved by them.** If the right
adjoints commute with the fully faithful functors `iC`, `iD`, and the left adjoint `L'` maps the
image of `iC` into the essential image of `iD`, then the left adjoints commute with `iC`, `iD`:
`iC ⋙ L' ≅ L ⋙ iD`. -/
noncomputable def compIsoOfForallMemEssImage : iC ⋙ L' ≅ L ⋙ iD :=
  have := hiD.full
  have := hiD.faithful
  (Functor.essImage.liftFunctorCompIso (iC ⋙ L') iD h).symm ≪≫
    Functor.isoWhiskerRight
      ((adj'.restrictFullyFaithful hiC hiD
        (Functor.essImage.liftFunctorCompIso (iC ⋙ L') iD h).symm comm).leftAdjointUniq adj) iD

end CategoryTheory.Adjunction
