/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPlusSquare
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso

/-!
# The derived pullback squares are induced by the underived ones

For a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

the identifications `θ : f'^* g^* ≅ g'^* f^*` of the derived pullbacks used by the étale
(`AlgebraicGeometry.Etale.pullbackSquareComparison`) and by the pro-étale
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarSquareIso`) exchange maps are induced by the
underived identifications `AlgebraicGeometry.Etale.squareUpperStarIso` and
`AlgebraicGeometry.ProEtale.upperStarCompIso`, in the sense of
`CategoryTheory.Functor.mapDerivedCategorySquareIso`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The pullback comparison `θ_sq` of étale sheaves on bounded below derived categories is the
restriction of the square induced on unbounded derived categories by the underived square
isomorphism `AlgebraicGeometry.Etale.squareUpperStarIso`. -/
lemma Etale.ι_map_pullbackSquareComparison_hom_app (sq : CommSq g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)) :
    DerivedCategory.Plus.ι.map ((Etale.pullbackSquareComparison A sq).hom.app M) =
      (Functor.mapDerivedCategorySquareIso (Etale.squareUpperStarIso A sq)).hom.app
        (DerivedCategory.Plus.ι.obj M) := by
  rw [Etale.pullbackSquareComparison_eq]
  simp only [Etale.upperStarCompDerivedPlus, Etale.squareUpperStarIso,
    Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    NatTrans.comp_app, Functor.map_comp, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm, Functor.ι_map_mapDerivedCategoryPlusCompIso_inv_app,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_inv_app,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app, Category.assoc]

section ProEtale

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

/-- The composition isomorphism `L(h₁ ≫ h₂)^* ≅ Lh₂^* ⋙ Lh₁^*` is, modulo the identifications
`Lh^* ≅ D(h^*)`, the isomorphism induced by the underived composition isomorphism. -/
lemma leftDerivedUpperStarComp_hom_app {T S R : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (P : DerivedCategory (Sheaf (ProEt.topology R) A)) :
    (leftDerivedUpperStarComp A h₁ h₂).hom.app P =
      (leftDerivedUpperStarIsoMapDerivedCategory A (h₁ ≫ h₂)).hom.app P ≫
        (Functor.mapDerivedCategoryTriangleIso (ProEtale.upperStarComp A h₁ h₂)).hom.app P ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A h₁).inv.app
          ((ProEtale.upperStar A h₂).mapDerivedCategory.obj P) ≫
        (ProEtale.upperStar A h₁).leftDerivedFunctor.map
          ((leftDerivedUpperStarIsoMapDerivedCategory A h₂).inv.app P) := by
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
    Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc, Iso.inv_hom_id_app_assoc, NatTrans.naturality]

/-- The isomorphism `Lh^* ≅ Lh'^*` for `h = h'` is, modulo the identifications
`Lh^* ≅ D(h^*)`, the isomorphism induced by the underived one. -/
lemma leftDerivedUpperStarCongr_hom_app {Z W : Scheme.{u}} {h h' : Z ⟶ W} (e : h = h')
    (P : DerivedCategory (Sheaf (ProEt.topology W) A)) :
    (leftDerivedUpperStarCongr A e).hom.app P =
      (leftDerivedUpperStarIsoMapDerivedCategory A h).hom.app P ≫
        (Functor.mapDerivedCategoryNatIso (ProEtale.upperStarCongr A e)).hom.app P ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A h').inv.app P := by
  subst e
  have h₀ := NatTrans.congr_app
    (Functor.mapDerivedCategoryNatIso_refl (F := ProEtale.upperStar A h)) P
  simp only [ProEtale.upperStarCongr, eqToIso_refl] at h₀ ⊢
  simp [h₀]

/-- The pullback comparison `θ_sq : Lf'^* Lg^* ≅ Lg'^* Lf^*` of pro-étale sheaves is, modulo
the identifications `Lh^* ≅ D(h^*)`, the square induced by the underived square isomorphism
`AlgebraicGeometry.ProEtale.upperStarCompIso`. -/
lemma mapDerivedCategorySquareIso_upperStarCompIso_hom_app (sq : CommSq g' f' f g)
    (P : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    (Functor.mapDerivedCategorySquareIso (ProEtale.upperStarCompIso A sq.w.symm)).hom.app P ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A g').inv.app
          ((ProEtale.upperStar A f).mapDerivedCategory.obj P) ≫
        (ProEtale.upperStar A g').leftDerivedFunctor.map
          ((leftDerivedUpperStarIsoMapDerivedCategory A f).inv.app P) =
      (leftDerivedUpperStarIsoMapDerivedCategory A f').inv.app
          ((ProEtale.upperStar A g).mapDerivedCategory.obj P) ≫
        (ProEtale.upperStar A f').leftDerivedFunctor.map
          ((leftDerivedUpperStarIsoMapDerivedCategory A g).inv.app P) ≫
        (leftDerivedUpperStarSquareIso A sq).hom.app P := by
  have hc : (leftDerivedUpperStarIsoMapDerivedCategory A f').inv.app
          ((ProEtale.upperStar A g).mapDerivedCategory.obj P) ≫
        (ProEtale.upperStar A f').leftDerivedFunctor.map
          ((leftDerivedUpperStarIsoMapDerivedCategory A g).inv.app P) ≫
        (leftDerivedUpperStarComp A f' g).inv.app P =
      (Functor.mapDerivedCategoryTriangleIso (ProEtale.upperStarComp A f' g)).inv.app P ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A (f' ≫ g)).inv.app P := by
    rw [← cancel_mono ((leftDerivedUpperStarComp A f' g).hom.app P)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [leftDerivedUpperStarComp_hom_app]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [leftDerivedUpperStarSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    reassoc_of% hc, leftDerivedUpperStarCongr_hom_app, leftDerivedUpperStarComp_hom_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, ProEtale.upperStarCompIso,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso,
    Iso.trans_inv, Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm]

end ProEtale

end ProEtale

end AlgebraicGeometry
