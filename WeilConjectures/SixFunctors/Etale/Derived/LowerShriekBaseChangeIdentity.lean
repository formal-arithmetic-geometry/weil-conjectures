/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangePaste
public import WeilConjectures.EtaleCohomology.Purity.Smooth.IdentitySquareBaseChange

/-!
# Compact-support base change along squares with identity sides

Two computations of the compact-support base change map `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`):

* for the square `𝟙 ≫ b = b ≫ 𝟙` it is the identity, through `L(𝟙)^* ≅ 𝟭`
  (`leftDerivedUpperStarId_inv_app_comp_rightDerivedLowerShriekBaseChangeMap_app`);
* for the square `u ≫ 𝟙 = u ≫ 𝟙` of a proper `u`, through `Ru_! ≅ Ru_*`, `R(𝟙)_! ≅ 𝟭`
  and `L(𝟙)^* ≅ 𝟭`, it is the unit of `Lu^* ⊣ Ru_*`
  (`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap_app_comp_eq_unit_app`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The derived base change map `Ex_*` of the square `u ≫ 𝟙 = u ≫ 𝟙` is, through `R(𝟙)_* ≅ 𝟭`
and `L(𝟙)^* ≅ 𝟭`, the unit of `Lu^* ⊣ Ru_*`. -/
theorem derivedBaseChangeMap_app_eq_unit_app {X Y : Scheme.{u}} (u : X ⟶ Y)
    (sq : CommSq u u (𝟙 Y) (𝟙 Y))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app K =
      (L((𝟙 Y)^*[ModuleCat.{u + 1} Λ])).map ((rightDerivedLowerStarIdNatIso Λ Y).hom.app K) ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).hom.app K ≫
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) u).unit.app K := by
  apply Adjunction.ext_of_comp_counit
    (adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) u)
  rw [derivedUpperStar_map_derivedBaseChangeMap_app_counit,
    derivedSquareUpperStarIso_hom_app_eq _ sq (u ≫ 𝟙 Y) rfl, Iso.inv_hom_id_app,
    Category.id_comp, derivedUpperStarLowerStarAdjunction_id_counit_app, Functor.map_comp,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  erw [(derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) u).left_triangle_components K]
  erw [Category.comp_id]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).hom.naturality _).symm

variable [Finite Λ]

/-- **The compact-support base change of the square `u ≫ 𝟙 = u ≫ 𝟙` is the unit** of
`Lu^* ⊣ Ru_*`, through `Ru_! ≅ Ru_*`, `R(𝟙)_! ≅ 𝟭` and `L(𝟙)^* ≅ 𝟭`. -/
theorem rightDerivedLowerShriekBaseChangeMap_app_comp_eq_unit_app {X Y : Scheme.{u}}
    (u : X ⟶ Y) [IsProper u] (sq : IsPullback u u (𝟙 Y) (𝟙 Y))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekBaseChangeMap Λ sq).app K ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) u).hom.app
          ((L((u)^*[ModuleCat.{u + 1} Λ])).obj K) =
      (L((𝟙 Y)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) Y).hom.app K) ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).hom.app K ≫
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) u).unit.app K := by
  -- iso-level unfolding (the hom-level `rfl` times out in the kernel)
  have hI : rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) Y =
      rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) (𝟙 Y) ≪≫
        rightDerivedLowerStarIdNatIso Λ Y := rfl
  rw [hI, Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    rightDerivedLowerShriekBaseChangeMap_app_comp_lowerStarIso,
    derivedBaseChangeMap_app_eq_unit_app]

/-- **The compact-support base change of the square `𝟙 ≫ b = b ≫ 𝟙` is the identity**, through
`L(𝟙)^* ≅ 𝟭`. -/
theorem leftDerivedUpperStarId_inv_app_comp_rightDerivedLowerShriekBaseChangeMap_app
    {X Y : Scheme.{u}} {b : X ⟶ Y} [HasCompactification b] [QuasiCompact b]
    (sq : IsPullback (𝟙 X) b b (𝟙 Y))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).inv.app
        ((R(b)_![ModuleCat.{u + 1} Λ]).obj K) ≫
      (rightDerivedLowerShriekBaseChangeMap Λ sq).app K =
      (R(b)_![ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).inv.app K) := by
  have hE := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  have hc (N : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (𝟙 Y) (𝟙 Y) (𝟙 Y)
        (Category.id_comp (𝟙 Y)).symm).hom.app N =
        (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).inv.app
          ((L((𝟙 Y)^*[ModuleCat.{u + 1} Λ])).obj N) :=
    (Iso.comp_hom_eq_id ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).app _)).1
      (leftDerivedUpperStarComp_id_left_hom_app _ (𝟙 Y) N)
  have hc' : (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (𝟙 X) (𝟙 X) (𝟙 X)
        (Category.id_comp (𝟙 X)).symm).inv.app K =
        (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app
          ((L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj K) :=
    ((Iso.hom_comp_eq_id ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.id_comp (𝟙 X)).symm).app K)).1
        (leftDerivedUpperStarComp_id_left_hom_app _ (𝟙 X) K)).symm
  have P := rightDerivedLowerShriekBaseChangeMap_paste_horiz (Λ := Λ) sq sq sq
    (Category.id_comp (𝟙 Y)).symm (Category.id_comp (𝟙 X)).symm K
  rw [hc, hc'] at P
  -- `ψ_M := ε⁻¹ ≫ Ex_!(M) ≫ Rb_!(ε)` satisfies `Ex_!(K) ≫ ψ_{L(𝟙)^* K} = Ex_!(K)`
  have h1 : (rightDerivedLowerShriekBaseChangeMap Λ sq).app K ≫
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).inv.app
        ((R(b)_![ModuleCat.{u + 1} Λ]).obj ((L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
      (rightDerivedLowerShriekBaseChangeMap Λ sq).app
        ((L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
      (R(b)_![ModuleCat.{u + 1} Λ]).map ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app
        ((L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj K)) =
      (rightDerivedLowerShriekBaseChangeMap Λ sq).app K := by
    have n1 : (rightDerivedLowerShriekBaseChangeMap Λ sq).app K ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).inv.app
          ((R(b)_![ModuleCat.{u + 1} Λ]).obj ((L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj K)) =
        (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).inv.app
          ((L((𝟙 Y)^*[ModuleCat.{u + 1} Λ])).obj ((R(b)_![ModuleCat.{u + 1} Λ]).obj K)) ≫
          (L((𝟙 Y)^*[ModuleCat.{u + 1} Λ])).map
            ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K) :=
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).inv.naturality _
    rw [reassoc_of% n1]
    exact P
  have h2 : (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).inv.app
        ((R(b)_![ModuleCat.{u + 1} Λ]).obj ((L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
      (rightDerivedLowerShriekBaseChangeMap Λ sq).app
        ((L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
      (R(b)_![ModuleCat.{u + 1} Λ]).map ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app
        ((L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj K)) = 𝟙 _ := by
    rw [← cancel_epi ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K), h1]
    exact (Category.comp_id _).symm
  -- naturality of `ψ` along `ε : L(𝟙)^* K ⟶ K`
  have h3 : (R(b)_![ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K) ≫
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).inv.app
        ((R(b)_![ModuleCat.{u + 1} Λ]).obj K) ≫
      (rightDerivedLowerShriekBaseChangeMap Λ sq).app K ≫
      (R(b)_![ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K) =
      ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).inv.app
        ((R(b)_![ModuleCat.{u + 1} Λ]).obj ((L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
      (rightDerivedLowerShriekBaseChangeMap Λ sq).app
        ((L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
      (R(b)_![ModuleCat.{u + 1} Λ]).map ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app
        ((L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj K))) ≫
      (R(b)_![ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K) := by
    have n1 : (R(b)_![ModuleCat.{u + 1} Λ]).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K) ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).inv.app
          ((R(b)_![ModuleCat.{u + 1} Λ]).obj K) =
        (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).inv.app
          ((R(b)_![ModuleCat.{u + 1} Λ]).obj ((L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
        (L((𝟙 Y)^*[ModuleCat.{u + 1} Λ])).map ((R(b)_![ModuleCat.{u + 1} Λ]).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K)) :=
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).inv.naturality _
    have n2 : (L((𝟙 Y)^*[ModuleCat.{u + 1} Λ])).map ((R(b)_![ModuleCat.{u + 1} Λ]).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K)) ≫
        (rightDerivedLowerShriekBaseChangeMap Λ sq).app K =
        (rightDerivedLowerShriekBaseChangeMap Λ sq).app
          ((L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
        (R(b)_![ModuleCat.{u + 1} Λ]).map ((L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K)) :=
      (rightDerivedLowerShriekBaseChangeMap Λ sq).naturality _
    have n3 : (L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K) ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K =
        (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app
          ((L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K :=
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.naturality _
    rw [reassoc_of% n1, reassoc_of% n2, ← Functor.map_comp, n3, Functor.map_comp]
    simp only [Category.assoc]
  have h4 : (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).inv.app
        ((R(b)_![ModuleCat.{u + 1} Λ]).obj K) ≫
      (rightDerivedLowerShriekBaseChangeMap Λ sq).app K ≫
      (R(b)_![ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K) = 𝟙 _ := by
    rw [← cancel_epi ((R(b)_![ModuleCat.{u + 1} Λ]).map
      ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K)), h3, h2, Category.id_comp]
    exact (Category.comp_id _).symm
  rw [← cancel_mono ((R(b)_![ModuleCat.{u + 1} Λ]).map
    ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K)), ← Functor.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.assoc]
  exact h4

end AlgebraicGeometry.Etale
