/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Transporting a counit to algebras with invertible structure morphism

Let `L : C ⥤ D` and `R : D ⥤ C` commute with endofunctors `F` of `C` and `G` of `D` through
isomorphisms `eL : L ⋙ G ≅ F ⋙ L` and `eR : R ⋙ F ≅ G ⋙ R`, and let `ε : L ⋙ R ⟶ 𝟭 C` be a natural
transformation compatible with them: `F (ε M)` is `ε (F M)` conjugated by `eR` and `R eL`. Then `ε`
induces a natural transformation `mapOfNatIso eL ⋙ mapOfNatIso eR ⟶ 𝟭` on the categories of
algebras with invertible structure morphism, with the same components.
-/

@[expose] public section

namespace CategoryTheory.Endofunctor.IsoAlgebra

universe v v' u u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D} {R : D ⥤ C}
  (eL : L ⋙ G ≅ F ⋙ L) (eR : R ⋙ F ≅ G ⋙ R) (ε : L ⋙ R ⟶ 𝟭 C)

/-- A natural transformation `ε : L ⋙ R ⟶ 𝟭` is *compatible* with the commutation isomorphisms
`eL` and `eR` if `F (ε M)` is `ε (F M)` conjugated by `eR` and `R eL`. -/
def CounitCompatible : Prop :=
  ∀ M : C, F.map (ε.app M) = eR.hom.app (L.obj M) ≫ R.map (eL.hom.app M) ≫ ε.app (F.obj M)

/-- The natural transformation `mapOfNatIso eL ⋙ mapOfNatIso eR ⟶ 𝟭` induced by a natural
transformation `ε : L ⋙ R ⟶ 𝟭` compatible with the commutation isomorphisms. -/
@[simps]
noncomputable def mapOfNatIsoCompCounit (eL : L ⋙ G ≅ F ⋙ L) (eR : R ⋙ F ≅ G ⋙ R)
    (ε : L ⋙ R ⟶ 𝟭 C) (hε : CounitCompatible eL eR ε) :
    mapOfNatIso eL ⋙ mapOfNatIso eR ⟶ 𝟭 (IsoAlgebra F) where
  app K := ObjectProperty.homMk
    { f := ε.app K.carrier
      h := by
        change F.map (ε.app K.carrier) ≫ K.str.hom =
          (((mapOfNatIso eR).obj ((mapOfNatIso eL).obj K))).str.hom ≫ ε.app K.carrier
        simp only [mapOfNatIso_obj_str, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
          Functor.map_comp, Category.assoc, mapOfNatIso_obj_carrier]
        rw [hε K.carrier]
        simp only [Category.assoc]
        congr 2
        exact (ε.naturality K.str.hom).symm }
  naturality _ _ f := ObjectProperty.hom_ext _ (Algebra.Hom.ext (ε.naturality f.hom.f))

/-- The transported counit is invertible at `K` if `ε` is invertible at the carrier of `K`. -/
lemma isIso_mapOfNatIsoCompCounit_app (eL : L ⋙ G ≅ F ⋙ L) (eR : R ⋙ F ≅ G ⋙ R)
    (ε : L ⋙ R ⟶ 𝟭 C) (hε : CounitCompatible eL eR ε) (K : IsoAlgebra F)
    [IsIso (ε.app K.carrier)] : IsIso ((mapOfNatIsoCompCounit eL eR ε hε).app K) := by
  have : IsIso ((Algebra.forget F).map ((Algebra.IsIsoStr F).ι.map ((mapOfNatIsoCompCounit eL eR ε hε).app K))) :=
    inferInstanceAs (IsIso (ε.app K.carrier))
  have := isIso_of_reflects_iso ((Algebra.IsIsoStr F).ι.map
    ((mapOfNatIsoCompCounit eL eR ε hε).app K)) (Algebra.forget F)
  exact isIso_of_fully_faithful (Algebra.IsIsoStr F).ι _

/-- The transported counit is an isomorphism if `ε` is. -/
noncomputable def mapOfNatIsoCompCounitIso (eL : L ⋙ G ≅ F ⋙ L) (eR : R ⋙ F ≅ G ⋙ R)
    (ε : L ⋙ R ⟶ 𝟭 C) (hε : CounitCompatible eL eR ε) [IsIso ε] :
    mapOfNatIso eL ⋙ mapOfNatIso eR ≅ 𝟭 (IsoAlgebra F) :=
  have (K : IsoAlgebra F) : IsIso ((mapOfNatIsoCompCounit eL eR ε hε).app K) :=
    isIso_mapOfNatIsoCompCounit_app eL eR ε hε K
  have : IsIso (mapOfNatIsoCompCounit eL eR ε hε) := NatIso.isIso_of_isIso_app _
  asIso (mapOfNatIsoCompCounit eL eR ε hε)

end CategoryTheory.Endofunctor.IsoAlgebra
