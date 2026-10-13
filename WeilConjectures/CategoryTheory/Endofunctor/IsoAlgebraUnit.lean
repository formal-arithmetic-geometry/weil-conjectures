/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCounit

/-!
# Transporting a unit to algebras with invertible structure morphism

Let `L : C ⥤ D` and `R : D ⥤ C` commute with endofunctors `F` of `C` and `G` of `D` through
isomorphisms `eL : L ⋙ G ≅ F ⋙ L` and `eR : R ⋙ F ≅ G ⋙ R`, and let `η : 𝟭 D ⟶ R ⋙ L` be a natural
transformation compatible with them: `η (G N)` is `G (η N)` followed by `eL` and `L eR`. Then `η`
induces a natural transformation `𝟭 ⟶ mapOfNatIso eR ⋙ mapOfNatIso eL` on the categories of
algebras with invertible structure morphism, with the same components.

If `R ⊣ L` and the counit is compatible with `eL` and `eR` (`CounitCompatible`), then so is the
unit (`unitCompatible_of_counitCompatible`).
-/

@[expose] public section

namespace CategoryTheory.Endofunctor.IsoAlgebra

universe v v' u u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D} {R : D ⥤ C}
  (eL : L ⋙ G ≅ F ⋙ L) (eR : R ⋙ F ≅ G ⋙ R) (η : 𝟭 D ⟶ R ⋙ L)

/-- A natural transformation `η : 𝟭 ⟶ R ⋙ L` is *compatible* with the commutation isomorphisms
`eL` and `eR` if `η (G N)` is `G (η N)` followed by `eL` and `L eR`. -/
def UnitCompatible : Prop :=
  ∀ N : D, G.map (η.app N) ≫ eL.hom.app (R.obj N) ≫ L.map (eR.hom.app N) = η.app (G.obj N)

/-- If `R ⊣ L` and the counit of the adjunction is compatible with the commutation isomorphisms
`eL` and `eR`, then so is the unit. -/
theorem unitCompatible_of_counitCompatible {eL : L ⋙ G ≅ F ⋙ L} {eR : R ⋙ F ≅ G ⋙ R}
    (adj : R ⊣ L) (h : CounitCompatible eL eR adj.counit) : UnitCompatible eL eR adj.unit := by
  intro N
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Functor.comp_obj, Category.assoc]
  have h₁ := adj.counit.naturality (eR.hom.app N)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at h₁
  rw [h₁]
  have h₂ : R.map (eL.hom.app (R.obj N)) ≫ adj.counit.app (F.obj (R.obj N)) =
      eR.inv.app (L.obj (R.obj N)) ≫ F.map (adj.counit.app (R.obj N)) := by
    rw [h (R.obj N), Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% h₂]
  have h₃ := eR.inv.naturality (adj.unit.app N)
  simp only [Functor.comp_map, Functor.comp_obj] at h₃
  rw [reassoc_of% h₃, ← F.map_comp_assoc]
  simp

/-- The natural transformation `𝟭 ⟶ mapOfNatIso eR ⋙ mapOfNatIso eL` induced by a natural
transformation `η : 𝟭 ⟶ R ⋙ L` compatible with the commutation isomorphisms. -/
@[simps]
noncomputable def mapOfNatIsoCompUnit (eL : L ⋙ G ≅ F ⋙ L) (eR : R ⋙ F ≅ G ⋙ R)
    (η : 𝟭 D ⟶ R ⋙ L) (hη : UnitCompatible eL eR η) :
    𝟭 (IsoAlgebra G) ⟶ mapOfNatIso eR ⋙ mapOfNatIso eL where
  app K := ObjectProperty.homMk
    { f := η.app K.carrier
      h := by
        change G.map (η.app K.carrier) ≫
            (((mapOfNatIso eL).obj ((mapOfNatIso eR).obj K))).str.hom =
          K.str.hom ≫ η.app K.carrier
        simp only [mapOfNatIso_obj_str, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
          Functor.map_comp, mapOfNatIso_obj_carrier]
        rw [reassoc_of% (hη K.carrier)]
        exact (η.naturality K.str.hom).symm }
  naturality _ _ f := ObjectProperty.hom_ext _ (Algebra.Hom.ext (η.naturality f.hom.f))

/-- The transported unit is invertible at `K` if `η` is invertible at the carrier of `K`. -/
lemma isIso_mapOfNatIsoCompUnit_app (eL : L ⋙ G ≅ F ⋙ L) (eR : R ⋙ F ≅ G ⋙ R)
    (η : 𝟭 D ⟶ R ⋙ L) (hη : UnitCompatible eL eR η) (K : IsoAlgebra G)
    [IsIso (η.app K.carrier)] : IsIso ((mapOfNatIsoCompUnit eL eR η hη).app K) := by
  have : IsIso ((Algebra.forget G).map
      ((Algebra.IsIsoStr G).ι.map ((mapOfNatIsoCompUnit eL eR η hη).app K))) :=
    inferInstanceAs (IsIso (η.app K.carrier))
  have := isIso_of_reflects_iso ((Algebra.IsIsoStr G).ι.map
    ((mapOfNatIsoCompUnit eL eR η hη).app K)) (Algebra.forget G)
  exact isIso_of_fully_faithful (Algebra.IsIsoStr G).ι _

end CategoryTheory.Endofunctor.IsoAlgebra
