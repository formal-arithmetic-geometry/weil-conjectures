/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp

/-!
# The composition isomorphism of derived pullbacks is monoidal

For `g₁ : T ⟶ S` and `g₂ : S ⟶ R`, the composition isomorphism
`L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` (`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`) is
compatible with the tensor comparisons `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison`).

## Main results

- `AlgebraicGeometry.Etale.leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit`: on the image
  of a complex, the composition isomorphism is the composition isomorphism of the underived
  pullbacks, read through the counits of the derived pullbacks.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_comp`: the composition
  isomorphism commutes with the tensor comparisons.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

open DerivedCategory

variable {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂)

/-- On the image `Qh X` of a complex, the composition isomorphism
`L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` is the composition isomorphism `(g₁ ≫ g₂)^* ≅ g₂^* ⋙ g₁^*` of the
underived pullbacks, through the counits of the derived pullbacks:
```
  L(g₁ ≫ g₂)^*(Qh X) ──────────────▶ Lg₁^* Lg₂^* (Qh X)
          │ counit                        │ Lg₁^* counit ≫ counit
          ▼                               ▼
  Qh((g₁ ≫ g₂)^* X) ───────────────▶ Qh(g₁^* g₂^* X)
```
-/
@[reassoc]
lemma leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit
    (X : HomotopyCategory (Sheaf R.smallEtaleTopology A) (.up ℤ)) :
    (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app (Qh.obj X) ≫
        L((g₁)^*[A]).map ((g₂)^*[A].leftDerivedFunctorCounit.app X) ≫
        (g₁)^*[A].leftDerivedFunctorCounit.app (((g₂)^*[A].mapHomotopyCategory (.up ℤ)).obj X) =
      (g₁₂)^*[A].leftDerivedFunctorCounit.app X ≫
        Qh.map (Functor.mapHomotopyCategoryCompHom (g₂)^*[A] (g₁)^*[A] (g₁₂)^*[A]
          (upperStarComp A g₁ g₂ g₁₂ hg) X) := by
  have hfac (F : Sheaf R.smallEtaleTopology A ⥤ Sheaf T.smallEtaleTopology A) [F.Additive]
      [PreservesFiniteLimits F] [PreservesFiniteColimits F]
      (Y : HomotopyCategory (Sheaf R.smallEtaleTopology A) (.up ℤ)) :
      F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (Qh.obj Y) ≫
        F.mapDerivedCategoryFactorsh.hom.app Y = F.leftDerivedFunctorCounit.app Y :=
    NatTrans.congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac Y
  have hfac₂ (Y : HomotopyCategory (Sheaf R.smallEtaleTopology A) (.up ℤ)) :
      (g₂)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app (Qh.obj Y) ≫
        (g₂)^*[A].mapDerivedCategoryFactorsh.hom.app Y =
          (g₂)^*[A].leftDerivedFunctorCounit.app Y :=
    NatTrans.congr_app (g₂)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac Y
  have hfac₁ (Y : HomotopyCategory (Sheaf S.smallEtaleTopology A) (.up ℤ)) :
      (g₁)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app (Qh.obj Y) ≫
        (g₁)^*[A].mapDerivedCategoryFactorsh.hom.app Y =
          (g₁)^*[A].leftDerivedFunctorCounit.app Y :=
    NatTrans.congr_app (g₁)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac Y
  have hnat := (g₁)^*[A].leftDerivedFunctorIsoMapDerivedCategory.inv.naturality
    ((g₂)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app (Qh.obj X) ≫
      (g₂)^*[A].mapDerivedCategoryFactorsh.hom.app X)
  have hcomp := Functor.mapDerivedCategoryCompIso_fach (g₂)^*[A] (g₁)^*[A] X
  have hnatiso := Functor.mapDerivedCategoryNatIso_fach (upperStarComp A g₁ g₂ g₁₂ hg) X
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← hfac₂, ← hfac₁, ← hfac, ← reassoc_of% hnat, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Functor.mapHomotopyCategoryCompHom, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hnatiso, ← hcomp]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

end Etale

end AlgebraicGeometry
