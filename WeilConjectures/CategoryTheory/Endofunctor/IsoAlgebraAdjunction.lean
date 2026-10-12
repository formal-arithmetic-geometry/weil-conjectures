/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Adjunctions of algebras with invertible structure morphism

Let `L ⊣ R` be an adjunction between `C` and `D`, and let `F : C ⥤ C`, `G : D ⥤ D` be
endofunctors with commutation isomorphisms `eL : L ⋙ G ≅ F ⋙ L` and `eR : R ⋙ F ≅ G ⋙ R`. If
`eR` is the mate of `eL⁻¹` under `L ⊣ R`, then the unit and the counit of `L ⊣ R` are compatible
with the structure isomorphisms, so the transports `IsoAlgebra.mapOfNatIso eL` and
`IsoAlgebra.mapOfNatIso eR` are again adjoint, with the same unit and counit.

We also restrict an adjunction to full subcategories preserved by both adjoints.

## Main definitions

- `CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction`: the adjunction
  `mapOfNatIso eL ⊣ mapOfNatIso eR`.
- `CategoryTheory.ObjectProperty.liftFullSubcategoryAdjunction`: the restriction of an
  adjunction to full subcategories.
-/

@[expose] public section

universe v v' u u'

open CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {eL : L ⋙ G ≅ F ⋙ L} {eR : R ⋙ F ≅ G ⋙ R}

include adj in
/-- If `eR` is the mate of `eL⁻¹`, the unit of `L ⊣ R` commutes with the commutation
isomorphisms: `F η ≫ eR ≫ R eL = η F`. -/
lemma map_unit_app_comp_of_mateEquiv
    (h : mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv) = TwoSquare.mk _ _ _ _ eR.hom) (X : C) :
    F.map (adj.unit.app X) ≫ eR.hom.app (L.obj X) ≫ R.map (eL.hom.app X) =
      adj.unit.app (F.obj X) := by
  have h₁ := unit_mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv) X
  rw [h] at h₁
  change _ ≫ eR.hom.app _ = _ ≫ R.map (eL.inv.app X) at h₁
  rw [reassoc_of% h₁, ← R.map_comp, Iso.inv_hom_id_app]
  exact (congrArg (_ ≫ ·) (R.map_id _)).trans (Category.comp_id _)

include adj in
/-- If `eR` is the mate of `eL⁻¹`, the counit of `L ⊣ R` commutes with the commutation
isomorphisms: `G ε = eL ≫ L eR ≫ ε G`. -/
lemma map_counit_app_eq_of_mateEquiv
    (h : mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv) = TwoSquare.mk _ _ _ _ eR.hom) (Y : D) :
    G.map (adj.counit.app Y) =
      eL.hom.app (R.obj Y) ≫ L.map (eR.hom.app Y) ≫ adj.counit.app (G.obj Y) := by
  have h₁ := mateEquiv_counit adj adj (TwoSquare.mk _ _ _ _ eL.inv) Y
  rw [h] at h₁
  change L.map (eR.hom.app Y) ≫ _ = eL.inv.app (R.obj Y) ≫ _ at h₁
  rw [h₁, Iso.hom_inv_id_app_assoc]

/-- **Adjunctions of algebras with invertible structure morphism.** An adjunction `L ⊣ R` with
commutation isomorphisms `eL : L ⋙ G ≅ F ⋙ L` and `eR : R ⋙ F ≅ G ⋙ R` such that `eR` is the
mate of `eL⁻¹` induces an adjunction `mapOfNatIso eL ⊣ mapOfNatIso eR`, with the unit and counit
of `L ⊣ R`. -/
noncomputable def mapOfNatIsoAdjunction
    (h : mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv) = TwoSquare.mk _ _ _ _ eR.hom) :
    mapOfNatIso eL ⊣ mapOfNatIso eR :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app K := ObjectProperty.homMk
            { f := adj.unit.app K.carrier
              h := by
                change F.map (adj.unit.app K.carrier) ≫ eR.hom.app (L.obj K.carrier) ≫
                    R.map (eL.hom.app K.carrier ≫ L.map K.obj.str) = K.obj.str ≫ _
                rw [R.map_comp, reassoc_of% (map_unit_app_comp_of_mateEquiv adj h K.carrier)]
                exact (adj.unit.naturality K.obj.str).symm }
          naturality _ _ φ := ObjectProperty.hom_ext _
            (Algebra.Hom.ext (adj.unit.naturality φ.hom.f)) }
      counit :=
        { app K := ObjectProperty.homMk
            { f := adj.counit.app K.carrier
              h := by
                change G.map (adj.counit.app K.carrier) ≫ K.obj.str =
                  (eL.hom.app (R.obj K.carrier) ≫ L.map (eR.hom.app K.carrier ≫
                    R.map K.obj.str)) ≫ adj.counit.app K.carrier
                rw [map_counit_app_eq_of_mateEquiv adj h, L.map_comp]
                simp only [Category.assoc]
                exact congrArg (fun t ↦ eL.hom.app (R.obj K.carrier) ≫
                  L.map (eR.hom.app K.carrier) ≫ t) (adj.counit.naturality K.obj.str).symm }
          naturality _ _ φ := ObjectProperty.hom_ext _
            (Algebra.Hom.ext (adj.counit.naturality φ.hom.f)) }
      left_triangle := NatTrans.ext (funext fun K ↦
        ObjectProperty.hom_ext (Algebra.IsIsoStr G) (Algebra.Hom.ext (by
          simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
            Functor.associator_hom_app, comp_hom_f,
            mapOfNatIso_map_hom_f, ObjectProperty.homMk_hom, Category.id_comp]
          exact adj.left_triangle_components K.carrier)))
      right_triangle := NatTrans.ext (funext fun K ↦
        ObjectProperty.hom_ext (Algebra.IsIsoStr F) (Algebra.Hom.ext (by
          simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
            Functor.associator_inv_app, comp_hom_f,
            mapOfNatIso_map_hom_f, ObjectProperty.homMk_hom, Category.id_comp]
          exact adj.right_triangle_components K.carrier))) }

variable (h : mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv) = TwoSquare.mk _ _ _ _ eR.hom)

/-- The unit of `mapOfNatIsoAdjunction` is the unit of `L ⊣ R`. -/
@[simp]
lemma mapOfNatIsoAdjunction_unit_app_hom_f (K : IsoAlgebra F) :
    ((mapOfNatIsoAdjunction adj h).unit.app K).hom.f = adj.unit.app K.carrier :=
  rfl

/-- The counit of `mapOfNatIsoAdjunction` is the counit of `L ⊣ R`. -/
@[simp]
lemma mapOfNatIsoAdjunction_counit_app_hom_f (K : IsoAlgebra G) :
    ((mapOfNatIsoAdjunction adj h).counit.app K).hom.f = adj.counit.app K.carrier :=
  rfl

end CategoryTheory.Endofunctor.IsoAlgebra

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
