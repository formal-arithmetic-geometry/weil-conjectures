/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfGraphProjectionData
import WeilConjectures.AlgebraicGeometry.SfGraphFirstProjectionSquare
import WeilConjectures.AlgebraicGeometry.SfGraphMiddleProjectionSquare
import WeilConjectures.AlgebraicGeometry.SfGraphSecondProjectionSquare

/-! # The graph-model projection square

## References

* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 0GL1](https://stacks.math.columbia.edu/tag/0GL1)
* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] derivedTensor sfCompactProjection sfGraphWordProjection
  sfGraphPresentationComparison sfGraphFirstSideIso sfGraphSecondSideIso sfGraphMiddleIso
  sfGraphFirstPresentation sfGraphSecondPresentation
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local implicit_reducible] EtaleGraphPresentation.functor

private theorem paste_graph_squares
    {C : Type*} [Category C] (T : C ⥤ C)
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : C}
    (e₁ : A₀ ≅ A₁) (em : A₁ ≅ A₂) (e₂ : A₃ ≅ A₂)
    (d₁ : B₀ ≅ B₁) (dm : B₁ ≅ B₂) (d₂ : B₃ ≅ B₂)
    (p₀ : T.obj A₀ ⟶ B₀) (p₁ : T.obj A₁ ⟶ B₁)
    (p₂ : T.obj A₂ ⟶ B₂) (p₃ : T.obj A₃ ⟶ B₃)
    (h₁ : T.map e₁.hom ≫ p₁ = p₀ ≫ d₁.hom)
    (hm : T.map em.hom ≫ p₂ = p₁ ≫ dm.hom)
    (h₂ : T.map e₂.hom ≫ p₂ = p₃ ≫ d₂.hom) :
    T.map (e₁.hom ≫ em.hom ≫ e₂.inv) ≫ p₃ =
      p₀ ≫ d₁.hom ≫ dm.hom ≫ d₂.inv := by
  apply (cancel_mono d₂.hom).1
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h₂, ← T.map_comp_assoc e₂.inv e₂.hom p₂,
    e₂.inv_hom_id, T.map_id, Category.id_comp]
  rw [hm, reassoc_of% h₁]

/-- The graph comparison intertwines projection on a compactification and successive
projection on the proper/open/proper word.
-/
theorem sfGraphCompactificationComparison_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (t : EtaleGraphPresentation f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((sfGraphPresentationComparison A c t).hom.app M)).app K ≫
      sfGraphWordProjection A t M K =
    sfCompactProjection A c M K ≫
      (sfGraphPresentationComparison A c t).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) := by
  let N := ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
    ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)
  rw [sfGraphPresentationComparison_stages]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  exact paste_graph_squares ((derivedTensor (ModuleCat.{u + 1} A) Y).flip.obj K)
    ((sfGraphFirstSideIso c t A).app M) ((sfGraphMiddleIso c t A).app M)
    ((sfGraphSecondSideIso c t A).app M)
    ((sfGraphFirstSideIso c t A).app N) ((sfGraphMiddleIso c t A).app N)
    ((sfGraphSecondSideIso c t A).app N)
    (sfCompactProjection A c M K)
    (sfGraphWordProjection A (sfGraphFirstPresentation c t) M K)
    (sfGraphWordProjection A (sfGraphSecondPresentation c t) M K)
    (sfGraphWordProjection A t M K)
    (sfGraphFirstSideIso_projection A c t M K)
    (sfGraphMiddleIso_projection A c t M K)
    (sfGraphSecondSideIso_projection A c t M K)

end AlgebraicGeometry.Etale
