/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!

# Derived Upper Star and Lower Star

# Main Results

- `AlgebraicGeometry.Etale.rightDerivedLowerStar` : total right derived of lower star, the
  generic `Functor.rightDerivedFunctor` applied to the underived pushforward `(g)_*[A]`,
  written `R((g)_*[A])`.

- `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` : total right derived of lower star on
  the bounded below derived category, written `R+((g)_*[A])`.

- `AlgebraicGeometry.Etale.upperStarIdDerivedPlus` and
  `AlgebraicGeometry.Etale.upperStarCompDerivedPlus`: the identity isomorphism
  `D(𝟙 V)^*⁺ ≅ 𝟭` and the composition isomorphism `D(h₁ ≫ h₂)^*⁺ ≅ D(h₂)^*⁺ ⋙ D(h₁)^*⁺` of
  the pullbacks on the bounded below derived categories.

- `AlgebraicGeometry.Etale.lowerStarIdDerivedPlus`: the identity isomorphism
  `R(𝟙 V)_*⁺ ≅ 𝟭` of the pushforward on the bounded below derived categories. The
  corresponding composition isomorphism is `Functor.rightDerivedFunctorPlusCompIso'`
  applied to `AlgebraicGeometry.Etale.lowerStarComp`.

- `AlgebraicGeometry.Etale.derivedPlus_unit_comp_upperStarIdDerivedPlus` and
  `AlgebraicGeometry.Etale.derivedPlus_unit_comp_upperStarCompDerivedPlus`: the units of
  the bounded below derived adjunctions `D(g)^*⁺ ⊣ R(g)_*⁺` are compatible with these
  identity and composition isomorphisms.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

section DerivedLowerStar

namespace Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The total right derived functor `Rg_* : D(Z_ét) ⥤ D(Y_ét)` of the pushforward
`g_*` along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of
étale sheaves. -/
noncomputable def rightDerivedLowerStar :
    DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (g)_*[A].rightDerivedFunctor

/-- The right derived functor `Rg_* : D⁺(Z_ét) ⥤ D⁺(Y_ét)` of the pushforward `g_*` on the
*bounded below* derived categories of étale sheaves.

Blueprint `def-weil-pbc-direct-image`: Direct image and its derived functor

The direct image `g_*` is `AlgebraicGeometry.Etale.lowerStar`, with
`(g_* F)(W) = F(W ×_Y Z)` (`AlgebraicGeometry.Etale.lowerStar_obj_val_obj`); this is its right
derived functor `Rg_* : D⁺(Z_ét) ⥤ D⁺(Y_ét)`, computed by injective resolutions, and
`R^q g_* F` is the `q`-th cohomology sheaf of `Rg_* F`. -/
noncomputable def rightDerivedLowerStarPlus :
    DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (g)_*[A].rightDerivedFunctorPlus

end Etale

end DerivedLowerStar

section IdentityAndComposition

namespace Etale

variable {Y : Scheme.{u}}

variable (V : Scheme.{u})

/-- The identity isomorphism `D(𝟙 V)^*⁺ ≅ 𝟭` of the pullback along the identity on the
bounded below derived categories, induced by `AlgebraicGeometry.Etale.upperStarId`. -/
noncomputable def upperStarIdDerivedPlus :
    ((𝟙 V)^*[A]).mapDerivedCategoryPlus ≅
      𝟭 (DerivedCategory.Plus (Sheaf V.smallEtaleTopology A)) :=
  Functor.mapDerivedCategoryPlusNatIso (Etale.upperStarId A V) ≪≫
    Functor.mapDerivedCategoryPlusIdIso _

/-- On the image of a bounded below complex, `AlgebraicGeometry.Etale.upperStarIdDerivedPlus`
is the factorization `Functor.mapDerivedCategoryPlusFactorsh` followed by the levelwise
image of `AlgebraicGeometry.Etale.upperStarId`. -/
lemma upperStarIdDerivedPlus_hom_app
    (K : HomotopyCategory.Plus (Sheaf V.smallEtaleTopology A)) :
    (upperStarIdDerivedPlus A V).hom.app (DerivedCategory.Plus.Qh.obj K) =
      ((𝟙 V)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A V).hom).app K) := by
  rw [upperStarIdDerivedPlus, Iso.trans_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh,
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]

variable {V}

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

/-- The composition isomorphism `D(h₁ ≫ h₂)^*⁺ ≅ D(h₂)^*⁺ ⋙ D(h₁)^*⁺` of the pullbacks on
the bounded below derived categories, induced by `AlgebraicGeometry.Etale.upperStarComp`. -/
noncomputable def upperStarCompDerivedPlus (h₁₂ : T ⟶ R := h₁ ≫ h₂)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂ := by cat_disch) :
    ((h₁₂)^*[A]).mapDerivedCategoryPlus ≅
      ((h₂)^*[A]).mapDerivedCategoryPlus ⋙ ((h₁)^*[A]).mapDerivedCategoryPlus :=
  Functor.mapDerivedCategoryPlusNatIso (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

omit [HasSmallSiteSheafify A] in
@[reassoc]
lemma upperStarCompDerivedPlus_hom_app_factorsh (h₁₂ : T ⟶ R := h₁ ≫ h₂)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂ := by cat_disch)
    (K : HomotopyCategory.Plus (Sheaf R.smallEtaleTopology A)) :
    (Etale.upperStarCompDerivedPlus A h₁ h₂ h₁₂ hh₁₂).hom.app
          (DerivedCategory.Plus.Qh.obj K) ≫
        ((h₁)^*[A]).mapDerivedCategoryPlus.map
          (((h₂)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        ((h₁)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
          (((h₂)^*[A]).mapHomotopyCategoryPlus.obj K) =
      ((h₁₂)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂).hom).app K) := by
  simp only [Etale.upperStarCompDerivedPlus, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh]
  rw [Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]

/-- **The derived unit for a composite morphism**: the unit of the bounded below derived
adjunction `D(h₁ ≫ h₂)^*⁺ ⊣ R(h₁ ≫ h₂)_*⁺` is, modulo the composition isomorphism
`AlgebraicGeometry.Etale.upperStarCompDerivedPlus` of the pullbacks, the composite of the
units of `D(h₂)^*⁺ ⊣ R(h₂)_*⁺` and `D(h₁)^*⁺ ⊣ R(h₁)_*⁺`, followed by the composition
isomorphism of the derived pushforwards. -/
lemma derivedPlus_unit_comp_upperStarCompDerivedPlus (h₁₂ : T ⟶ R := h₁ ≫ h₂)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂ := by cat_disch)
    (Z : DerivedCategory.Plus (Sheaf R.smallEtaleTopology A)) :
    haveI : (((h₁)_*[A])).PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
        (Etale.upperStarLowerStarAdjunction A h₁)
    (Etale.upperStarLowerStarAdjunction A h₁₂).derivedPlus.unit.app Z ≫
        ((h₁₂)_*[A]).rightDerivedFunctorPlus.map
          ((Etale.upperStarCompDerivedPlus A h₁ h₂ h₁₂ hh₁₂).hom.app Z) =
      (Etale.upperStarLowerStarAdjunction A h₂).derivedPlus.unit.app Z ≫
        ((h₂)_*[A]).rightDerivedFunctorPlus.map
          ((Etale.upperStarLowerStarAdjunction A h₁).derivedPlus.unit.app
            (((h₂)^*[A]).mapDerivedCategoryPlus.obj Z)) ≫
        (Functor.rightDerivedFunctorPlusCompIso' ((h₁)_*[A]) ((h₂)_*[A])
            (Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂)).hom.app
          (((h₁)^*[A]).mapDerivedCategoryPlus.obj
            (((h₂)^*[A]).mapDerivedCategoryPlus.obj Z)) := by
  have : (((h₁)_*[A])).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A h₁)
  have hXi : (Functor.rightDerivedFunctorPlusCompIso' ((h₁)_*[A]) ((h₂)_*[A])
        (Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂)).hom =
      (Functor.rightDerivedFunctorPlusCompIso ((h₁)_*[A]) ((h₂)_*[A])).inv ≫
        Functor.rightDerivedFunctorPlusNatTrans
          (Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂).hom := rfl
  have hC := Adjunction.derivedPlus_unit_comp_app
    (Etale.upperStarLowerStarAdjunction A h₁₂)
    ((Etale.upperStarLowerStarAdjunction A h₂).comp
      (Etale.upperStarLowerStarAdjunction A h₁))
    (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂) (Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂)
    (Etale.upperStarComp_hom_app_unit_app A h₁ h₂ · h₁₂ hh₁₂) Z
  have hcompunit := Adjunction.derivedPlus_comp_unit_app
    (Etale.upperStarLowerStarAdjunction A h₂) (Etale.upperStarLowerStarAdjunction A h₁) Z
  have hnatCI := (Functor.rightDerivedFunctorPlusCompIso ((h₁)_*[A]) ((h₂)_*[A])).inv.naturality
    ((Functor.mapDerivedCategoryPlusCompIso ((h₂)^*[A]) ((h₁)^*[A])).hom.app Z)
  have hnatN := (Functor.rightDerivedFunctorPlusNatTrans
      (Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂).hom).naturality
    ((Functor.mapDerivedCategoryPlusCompIso ((h₂)^*[A]) ((h₁)^*[A])).hom.app Z)
  simp only [Functor.comp_obj, Functor.comp_map] at hnatCI hnatN
  have hPhi : (Etale.upperStarCompDerivedPlus A h₁ h₂ h₁₂ hh₁₂).hom.app Z =
      (Functor.mapDerivedCategoryPlusNatIso
          (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂)).hom.app Z ≫
        (Functor.mapDerivedCategoryPlusCompIso ((h₂)^*[A]) ((h₁)^*[A])).hom.app Z := rfl
  rw [hPhi, Functor.map_comp, ← Category.assoc, hC, Category.assoc, ← hnatN,
    ← reassoc_of% hcompunit, hXi]
  simp only [NatTrans.comp_app]
  rw [reassoc_of% hnatCI, Iso.hom_inv_id_app_assoc]

end Etale

end IdentityAndComposition

end AlgebraicGeometry
