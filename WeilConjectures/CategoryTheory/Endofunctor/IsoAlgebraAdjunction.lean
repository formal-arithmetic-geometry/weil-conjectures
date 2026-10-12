/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Transport of adjunctions to algebras with invertible structure morphism

Let `L ⊣ R` be an adjunction between `C` and `D`, and let `F : C ⥤ C` and `G : D ⥤ D` be
endofunctors with commutation isomorphisms `eL : L ⋙ G ≅ F ⋙ L` and `eR : R ⋙ F ≅ G ⋙ R`. If
`eR` is the mate of `eL⁻¹` under `L ⊣ R`, then the unit and the counit of `L ⊣ R` are morphisms
of algebras, and the transports `mapOfNatIso eL ⊣ mapOfNatIso eR` are adjoint
(`CategoryTheory.Endofunctor.IsoAlgebra.adjunctionMapOfNatIso`), with the unit and counit of
`L ⊣ R` as underlying unit and counit.
-/

@[expose] public section

universe v v' u u'

open CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (eL : L ⋙ G ≅ F ⋙ L) (eR : R ⋙ F ≅ G ⋙ R)

/-- The unit of `L ⊣ R` at the underlying object of an algebra, as a morphism of algebras. -/
noncomputable def adjunctionMapOfNatIsoUnitApp
    (h : (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv)).natTrans = eR.hom)
    (K : IsoAlgebra F) : K ⟶ (mapOfNatIso eR).obj ((mapOfNatIso eL).obj K) :=
  ObjectProperty.homMk
    { f := adj.unit.app K.carrier
      h := by
        have hu : F.map (adj.unit.app K.carrier) ≫ eR.hom.app (L.obj K.carrier) =
            adj.unit.app (F.obj K.carrier) ≫ R.map (eL.inv.app K.carrier) := by
          rw [← h]
          exact unit_mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv) K.carrier
        change F.map (adj.unit.app K.carrier) ≫ eR.hom.app (L.obj K.carrier) ≫
          R.map (eL.hom.app K.carrier ≫ L.map K.obj.str) = K.obj.str ≫ adj.unit.app K.carrier
        rw [reassoc_of% hu]
        simp only [Functor.comp_obj, Functor.map_comp,
          ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
        exact (adj.unit.naturality K.obj.str).symm }

/-- The counit of `L ⊣ R` at the underlying object of an algebra, as a morphism of algebras. -/
noncomputable def adjunctionMapOfNatIsoCounitApp
    (h : (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv)).natTrans = eR.hom)
    (K : IsoAlgebra G) : (mapOfNatIso eL).obj ((mapOfNatIso eR).obj K) ⟶ K :=
  ObjectProperty.homMk
    { f := adj.counit.app K.carrier
      h := by
        have hc : L.map (eR.hom.app K.carrier) ≫ adj.counit.app (G.obj K.carrier) =
            eL.inv.app (R.obj K.carrier) ≫ G.map (adj.counit.app K.carrier) := by
          rw [← h]
          exact mateEquiv_counit adj adj (TwoSquare.mk _ _ _ _ eL.inv) K.carrier
        change G.map (adj.counit.app K.carrier) ≫ K.obj.str =
          (eL.hom.app (R.obj K.carrier) ≫ L.map (eR.hom.app K.carrier ≫ R.map K.obj.str)) ≫
            adj.counit.app K.carrier
        simp only [Functor.map_comp, Category.assoc]
        rw [show L.map (R.map K.obj.str) ≫ adj.counit.app K.carrier =
            adj.counit.app _ ≫ K.obj.str from adj.counit.naturality K.obj.str, reassoc_of% hc]
        simp }

/-- **Transport of an adjunction to algebras.** If `eR : R ⋙ F ≅ G ⋙ R` is the mate of
`eL⁻¹ : F ⋙ L ⟶ L ⋙ G` under `L ⊣ R`, then `mapOfNatIso eL ⊣ mapOfNatIso eR`, with the unit and
counit of `L ⊣ R` as underlying unit and counit. -/
noncomputable def adjunctionMapOfNatIso
    (h : (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv)).natTrans = eR.hom) :
    mapOfNatIso eL ⊣ mapOfNatIso eR :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app := adjunctionMapOfNatIsoUnitApp adj eL eR h
          naturality _ _ φ := ObjectProperty.hom_ext _ (Algebra.Hom.ext (by
            exact adj.unit.naturality φ.hom.f)) }
      counit :=
        { app := adjunctionMapOfNatIsoCounitApp adj eL eR h
          naturality _ _ φ := ObjectProperty.hom_ext _ (Algebra.Hom.ext (by
            exact adj.counit.naturality φ.hom.f)) }
      left_triangle := by
        ext K
        apply ObjectProperty.hom_ext
        apply Algebra.Hom.ext
        simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, Functor.whiskerRight_app,
          Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp, comp_hom_f,
          mapOfNatIso_map_hom_f]
        exact adj.left_triangle_components K.carrier
      right_triangle := by
        ext K
        apply ObjectProperty.hom_ext
        apply Algebra.Hom.ext
        simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, Functor.whiskerRight_app,
          Functor.associator_inv_app, Functor.whiskerLeft_app, Category.id_comp, comp_hom_f,
          mapOfNatIso_map_hom_f]
        exact adj.right_triangle_components K.carrier }

@[simp]
lemma adjunctionMapOfNatIso_unit_app_hom_f
    (h : (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv)).natTrans = eR.hom) (K : IsoAlgebra F) :
    ((adjunctionMapOfNatIso adj eL eR h).unit.app K).hom.f = adj.unit.app K.carrier :=
  rfl

@[simp]
lemma adjunctionMapOfNatIso_counit_app_hom_f
    (h : (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv)).natTrans = eR.hom) (K : IsoAlgebra G) :
    ((adjunctionMapOfNatIso adj eL eR h).counit.app K).hom.f = adj.counit.app K.carrier :=
  rfl

end CategoryTheory.Endofunctor.IsoAlgebra
