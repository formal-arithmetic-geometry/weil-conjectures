/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange

/-!
# The projection formula for the extension by zero and refinements

For a refinement `r : c.Refinement d` of compactifications whose square over `X` is cartesian,
with `q = r.hom`, the projection formula for `D(d.i)_!` pulled back along `Lq^*` is the
projection formula for `D(c.i)_!`, through the base change isomorphism
`D(c.i)_! ≅ D(d.i)_! ⋙ Dq^*` (`AlgebraicGeometry.Etale.refinementLowerShriekBaseChangeDerivedIso`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

set_option maxHeartbeats 1000000 in
-- The tensor comparisons of the derived pullbacks make this rewriting expensive.
omit [HasSmallSiteSheafify A] in
/-- The square map of a refinement is compatible with the comparisons
`Dj^*X ⊗ᴸ Lj^*Y ≅ Dj^*(X ⊗ᴸ Y)` and the tensor comparison of `Lq^*`. -/
lemma refinementSquareMap_tensor (M N : DerivedCategory (Sheaf d.Z.smallEtaleTopology A)) :
    ((mapDerivedCategoryUpperStarDerivedTensorIso A d.i).hom.app M).app N ≫
        (refinementSquareMap A r).app (((-⊗ᴸ-(d.Z)[A]).obj M).obj N) ≫
        D((c.i)^*[A]).map (((leftDerivedUpperStarTensorComparison A r.hom).app M).app N) =
      ((-⊗ᴸ-(X)[A]).map ((refinementSquareMap A r).app M)).app _ ≫
        ((-⊗ᴸ-(X)[A]).obj _).map
          ((leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app N) ≫
        ((mapDerivedCategoryUpperStarDerivedTensorIso A c.i).hom.app
          (L((r.hom)^*[A]).obj M)).app (L((r.hom)^*[A]).obj N) := by
  rw [refinementSquareMap_app, refinementSquareMap_app]
  simp only [mapDerivedCategoryUpperStarDerivedTensorIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom, Functor.whiskeringLeft₂_map_app_app_app_app,
    Functor.postcompose₂_map_app_app_app, Functor.map_comp, Category.assoc]
  have key₀ : ((leftDerivedUpperStarTensorNatIso A d.i).inv.app M).app N ≫
      (leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app
        (((-⊗ᴸ-(d.Z)[A]).obj M).obj N) ≫
      L((c.i)^*[A]).map (((leftDerivedUpperStarTensorComparison A r.hom).app M).app N) =
      ((leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app M ⊗ₘ
        (leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app N) ≫
      ((leftDerivedUpperStarTensorNatIso A c.i).inv.app (L((r.hom)^*[A]).obj M)).app
        (L((r.hom)^*[A]).obj N) := by
    have h := leftDerivedUpperStarTensorComparison_comp A c.i r.hom d.i r.i_hom.symm M N
    change (leftDerivedUpperStarTensorIso A d.i M N).inv ≫ _ =
      _ ≫ (leftDerivedUpperStarTensorIso A c.i _ _).inv
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, leftDerivedUpperStarTensorIso_hom,
      leftDerivedUpperStarTensorIso_hom]
    rw [Category.assoc]
    exact h.symm
  have c₂ : L((c.i)^*[A]).map (((leftDerivedUpperStarTensorComparison A r.hom).app M).app N) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory A c.i).hom.app
        (((-⊗ᴸ-(c.Z)[A]).obj (L((r.hom)^*[A]).obj M)).obj (L((r.hom)^*[A]).obj N)) =
      (leftDerivedUpperStarIsoMapDerivedCategory A c.i).hom.app
        (L((r.hom)^*[A]).obj (((-⊗ᴸ-(d.Z)[A]).obj M).obj N)) ≫
      D((c.i)^*[A]).map (((leftDerivedUpperStarTensorComparison A r.hom).app M).app N) :=
    (leftDerivedUpperStarIsoMapDerivedCategory A c.i).hom.naturality _
  rw [Iso.hom_inv_id_app_assoc]
  erw [← c₂]
  rw [reassoc_of% key₀]
  simp only [derivedTensor, curriedTensor_map_app, curriedTensor_obj_map]
  have w : (leftDerivedUpperStarIsoMapDerivedCategory A c.i).hom.app (L((r.hom)^*[A]).obj M) ▷
      L((d.i)^*[A]).obj N ≫
      D((c.i)^*[A]).obj (L((r.hom)^*[A]).obj M) ◁
        (leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app N ≫
      (leftDerivedUpperStarIsoMapDerivedCategory A c.i).inv.app (L((r.hom)^*[A]).obj M) ▷
        L((c.i)^*[A]).obj (L((r.hom)^*[A]).obj N) =
      L((c.i)^*[A]).obj (L((r.hom)^*[A]).obj M) ◁
        (leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app N := by
    rw [← whisker_exchange_assoc]
    dsimp only [Functor.comp_obj]
    rw [← comp_whiskerRight, Iso.hom_inv_id_app, id_whiskerRight, Category.comp_id]
  dsimp only [Functor.comp_obj]
  simp only [reassoc_of% w]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]

end Etale

end AlgebraicGeometry
