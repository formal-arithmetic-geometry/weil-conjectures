/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra

/-!
# Lifting adjunctions to algebras with invertible structure morphism

Let `L ⊣ R` be an adjunction between `C` and `D`, `F` and `G` endofunctors of `C` and `D`, and
`eL : L ⋙ G ≅ F ⋙ L`, `eR : R ⋙ F ≅ G ⋙ R` commutation isomorphisms. If `eR` is the mate of
`eL⁻¹` (`CategoryTheory.mateEquiv`), the transported functors
`IsoAlgebra.mapOfNatIso eL : IsoAlgebra F ⥤ IsoAlgebra G` and
`IsoAlgebra.mapOfNatIso eR : IsoAlgebra G ⥤ IsoAlgebra F` are adjoint, the unit and the counit
having the unit and the counit of `L ⊣ R` as underlying morphisms
(`CategoryTheory.Endofunctor.IsoAlgebra.adjunction`).

If `F` and `G` are equivalences, the mate of `eL⁻¹` is an isomorphism
(`CategoryTheory.Endofunctor.IsoAlgebra.mateIso`), so every `eL` lifts `L ⊣ R`.

This is used for the equivariance of the adjunctions `φ^* ⊣ φ_*` of Weil sheaves (blueprint
`prop-sf-localization-all-stages`, Weil clause).

## Main definitions

- `CategoryTheory.Endofunctor.IsoAlgebra.adjunction`: `mapOfNatIso eL ⊣ mapOfNatIso eR`.
- `CategoryTheory.Endofunctor.IsoAlgebra.mateIso`: the mate of `eL⁻¹`, an isomorphism when `F`
  and `G` are equivalences.
-/

@[expose] public section

universe v v' u u'

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {eL : L ⋙ G ≅ F ⋙ L} {eR : R ⋙ F ≅ G ⋙ R}

include adj in
/-- The unit form of the mate condition `mateEquiv adj adj eL⁻¹ = eR`. -/
@[reassoc]
lemma map_unit_app_comp_of_mateEquiv_eq (h : mateEquiv adj adj eL.inv = eR.hom) (X : C) :
    F.map (adj.unit.app X) ≫ eR.hom.app (L.obj X) ≫ R.map (eL.hom.app X) =
      adj.unit.app (F.obj X) := by
  have := unit_mateEquiv adj adj eL.inv X
  rw [h] at this
  erw [reassoc_of% this, ← R.map_comp, Iso.inv_hom_id_app, R.map_id, Category.comp_id]

include adj in
/-- The counit form of the mate condition `mateEquiv adj adj eL⁻¹ = eR`. -/
@[reassoc]
lemma comp_map_counit_app_of_mateEquiv_eq (h : mateEquiv adj adj eL.inv = eR.hom) (Y : D) :
    eL.hom.app (R.obj Y) ≫ L.map (eR.hom.app Y) ≫ adj.counit.app (G.obj Y) =
      G.map (adj.counit.app Y) := by
  have := mateEquiv_counit adj adj eL.inv Y
  rw [h] at this
  erw [this, Iso.hom_inv_id_app_assoc]

variable {adj}

/-- The unit of `mapOfNatIso eL ⊣ mapOfNatIso eR`, with underlying morphisms the unit of
`L ⊣ R`. -/
noncomputable def adjunctionUnit (h : mateEquiv adj adj eL.inv = eR.hom) :
    𝟭 (IsoAlgebra F) ⟶ mapOfNatIso eL ⋙ mapOfNatIso eR where
  app K := ObjectProperty.homMk
    { f := adj.unit.app K.carrier
      h := by
        change F.map (adj.unit.app K.carrier) ≫ eR.hom.app (L.obj K.carrier) ≫
          R.map (eL.hom.app K.carrier ≫ L.map K.str.hom) = K.str.hom ≫ adj.unit.app K.carrier
        rw [R.map_comp]
        erw [map_unit_app_comp_of_mateEquiv_eq_assoc adj h]
        exact (adj.unit.naturality K.str.hom).symm }
  naturality _ _ φ := ObjectProperty.hom_ext _ (Algebra.Hom.ext (adj.unit.naturality φ.hom.f))

/-- The counit of `mapOfNatIso eL ⊣ mapOfNatIso eR`, with underlying morphisms the counit of
`L ⊣ R`. -/
noncomputable def adjunctionCounit (h : mateEquiv adj adj eL.inv = eR.hom) :
    mapOfNatIso eR ⋙ mapOfNatIso eL ⟶ 𝟭 (IsoAlgebra G) where
  app K := ObjectProperty.homMk
    { f := adj.counit.app K.carrier
      h := by
        change G.map (adj.counit.app K.carrier) ≫ K.str.hom =
          (eL.hom.app (R.obj K.carrier) ≫ L.map (eR.hom.app K.carrier ≫ R.map K.str.hom)) ≫
            adj.counit.app K.carrier
        rw [← comp_map_counit_app_of_mateEquiv_eq adj h, L.map_comp]
        simp only [Category.assoc]
        erw [adj.counit_naturality] }
  naturality _ _ φ := ObjectProperty.hom_ext _ (Algebra.Hom.ext (adj.counit.naturality φ.hom.f))

/-- **Lifting an adjunction to algebras.** If `eR` is the mate of `eL⁻¹`, the adjunction
`L ⊣ R` lifts to an adjunction `mapOfNatIso eL ⊣ mapOfNatIso eR` between the categories of
algebras with invertible structure morphism, whose unit and counit have the unit and counit of
`L ⊣ R` as underlying morphisms. This gives the Frobenius-equivariant adjunctions `φ^* ⊣ φ_*` of
Weil sheaves (blueprint `prop-sf-localization-all-stages`, Weil clause). -/
noncomputable def adjunction (h : mateEquiv adj adj eL.inv = eR.hom) :
    mapOfNatIso eL ⊣ mapOfNatIso eR where
  unit := adjunctionUnit h
  counit := adjunctionCounit h
  left_triangle_components K :=
    ObjectProperty.hom_ext _ (Algebra.Hom.ext (by exact adj.left_triangle_components K.carrier))
  right_triangle_components K :=
    ObjectProperty.hom_ext _ (Algebra.Hom.ext (by exact adj.right_triangle_components K.carrier))

@[simp]
lemma adjunction_unit_app_hom_f (h : mateEquiv adj adj eL.inv = eR.hom) (K : IsoAlgebra F) :
    ((adjunction h).unit.app K).hom.f = adj.unit.app K.carrier :=
  rfl

@[simp]
lemma adjunction_counit_app_hom_f (h : mateEquiv adj adj eL.inv = eR.hom) (K : IsoAlgebra G) :
    ((adjunction h).counit.app K).hom.f = adj.counit.app K.carrier :=
  rfl

/-- The forgetful functor maps the unit of the lifted adjunction to the unit of `L ⊣ R`. -/
lemma forget_map_adjunction_unit_app (h : mateEquiv adj adj eL.inv = eR.hom)
    (K : IsoAlgebra F) : (forget F).map ((adjunction h).unit.app K) = adj.unit.app K.carrier :=
  rfl

/-- The forgetful functor maps the counit of the lifted adjunction to the counit of `L ⊣ R`. -/
lemma forget_map_adjunction_counit_app (h : mateEquiv adj adj eL.inv = eR.hom)
    (K : IsoAlgebra G) : (forget G).map ((adjunction h).counit.app K) = adj.counit.app K.carrier :=
  rfl

/-- If the counit of `L ⊣ R` is an isomorphism, so is the counit of the lifted adjunction. -/
instance isIso_adjunction_counit [IsIso adj.counit]
    (h : mateEquiv adj adj eL.inv = eR.hom) : IsIso (adjunction h).counit := by
  have (K : IsoAlgebra G) : IsIso ((adjunction h).counit.app K) := by
    have : IsIso ((forget G).map ((adjunction h).counit.app K)) := by
      rw [forget_map_adjunction_counit_app]
      exact NatIso.isIso_app_of_isIso adj.counit _
    exact isIso_of_reflects_iso _ (forget G)
  exact NatIso.isIso_of_isIso_app _

/-- If the unit of `L ⊣ R` is an isomorphism, so is the unit of the lifted adjunction. -/
instance isIso_adjunction_unit [IsIso adj.unit]
    (h : mateEquiv adj adj eL.inv = eR.hom) : IsIso (adjunction h).unit := by
  have (K : IsoAlgebra F) : IsIso ((adjunction h).unit.app K) := by
    have : IsIso ((forget F).map ((adjunction h).unit.app K)) := by
      rw [forget_map_adjunction_unit_app]
      exact NatIso.isIso_app_of_isIso adj.unit _
    exact isIso_of_reflects_iso _ (forget F)
  exact NatIso.isIso_of_isIso_app _

section Equivalence

variable (adj) (eL) [F.IsEquivalence] [G.IsEquivalence]

/-- If `F` and `G` are equivalences, the mate `R ⋙ F ⟶ G ⋙ R` of `eL⁻¹` is an isomorphism: its
mate along the adjunctions `F ⊣ F⁻¹` and `G ⊣ G⁻¹` is the conjugate of `eL⁻¹`
(`CategoryTheory.iterated_mateEquiv_conjugateEquiv`), an isomorphism, and the units and counits
of these adjunctions are isomorphisms. -/
instance isIso_mateEquiv : IsIso (mateEquiv adj adj eL.inv).natTrans := by
  have hγ : IsIso (mateEquiv G.asEquivalence.toAdjunction F.asEquivalence.toAdjunction
      (mateEquiv adj adj eL.inv)).natTrans := by
    erw [iterated_mateEquiv_conjugateEquiv adj adj F.asEquivalence.toAdjunction
      G.asEquivalence.toAdjunction eL.inv]
    exact conjugateEquiv_iso _ _ (α := (eL.inv : F ⋙ L ⟶ L ⋙ G))
  set β := mateEquiv adj adj eL.inv
  set γ := mateEquiv G.asEquivalence.toAdjunction F.asEquivalence.toAdjunction β
  have hβ : β = (mateEquiv G.asEquivalence.toAdjunction F.asEquivalence.toAdjunction).symm γ :=
    ((mateEquiv _ _).symm_apply_apply β).symm
  have (Y : D) : IsIso (β.natTrans.app Y) := by
    rw [hβ]
    have : ∀ Z, IsIso (γ.natTrans.app Z) := fun Z ↦ @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hγ Z
    simp only [mateEquiv_symm_apply, TwoSquare.mk, NatTrans.comp_app, Functor.comp_obj,
      Functor.id_obj, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, Category.id_comp, Category.comp_id, Functor.map_id,
      Equivalence.toAdjunction_unit, Equivalence.toAdjunction_counit]
    have h1 : IsIso ((R ⋙ F.asEquivalence.functor).map (G.asEquivalence.unit.app Y)) :=
      inferInstance
    have h2 : IsIso (F.asEquivalence.counit.app (R.obj (G.asEquivalence.functor.obj Y))) :=
      inferInstance
    repeat' refine IsIso.comp_isIso' ?_ ?_
    all_goals first | exact IsIso.id _ | exact h1 | exact h2 | exact Functor.map_isIso _ _
  exact NatIso.isIso_of_isIso_app _

/-- If `F` and `G` are equivalences, the mate `R ⋙ F ≅ G ⋙ R` of `eL⁻¹`. -/
noncomputable def mateIso : R ⋙ F ≅ G ⋙ R :=
  asIso (mateEquiv adj adj eL.inv).natTrans

lemma mateEquiv_inv_eq_mateIso_hom : mateEquiv adj adj eL.inv = (mateIso adj eL).hom :=
  rfl

end Equivalence

end CategoryTheory.Endofunctor.IsoAlgebra
