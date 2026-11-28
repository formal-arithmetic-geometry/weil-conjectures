/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeIdentity
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompIsoUnit

/-!
# Compact-support base change along a square of isomorphisms

Let `g ≫ a = a' ≫ h` be a cartesian square with `g` and `h` isomorphisms. The compact-support
base change map `Ex_! : Lh^* Ra_! ⟶ Ra'_! Lg^*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`) is adjoint, under
`Lh^* ⊣ Rh_*`, to the composite
```
Ra_! ⟶ Ra_! Rg_* Lg^* ≅ Ra_! Rg_! Lg^* ≅ R(g ≫ a)_! Lg^* = R(a' ≫ h)_! Lg^* ≅ Rh_! Ra'_! Lg^*
  ≅ Rh_* Ra'_! Lg^*
```
of the unit of `Lg^* ⊣ Rg_*`, the identifications `Rg_! ≅ Rg_*`, `Rh_! ≅ Rh_*` and the
composition isomorphisms of the lower shriek
(`AlgebraicGeometry.Etale.unit_app_comp_map_rightDerivedLowerShriekBaseChangeMap_app`).

The proof stacks the square on the square `h ≫ 𝟙 = h ≫ 𝟙` and the resulting square on the
square `𝟙 ≫ a = a ≫ 𝟙`, and uses the vertical pasting of the compact-support base change maps
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap_paste_vert`) together with their
values on squares with identity sides.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

section Congr

@[reassoc]
lemma rightDerivedLowerShriekCongrIso_hom_app_trans {X Y : Scheme.{u}} {f₁ f₂ f₃ : X ⟶ Y}
    [HasCompactification f₁] [HasCompactification f₂] [HasCompactification f₃]
    (e₁ : f₁ = f₂) (e₂ : f₂ = f₃)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekCongrIso Λ e₁).hom.app K ≫
        (rightDerivedLowerShriekCongrIso Λ e₂).hom.app K =
      (rightDerivedLowerShriekCongrIso Λ (e₁.trans e₂)).hom.app K := by
  subst e₁ e₂
  exact Category.id_comp _

lemma rightDerivedLowerShriekCongrIso_inv {X Y : Scheme.{u}} {f₁ f₂ : X ⟶ Y}
    [HasCompactification f₁] [HasCompactification f₂] (e : f₁ = f₂) :
    (rightDerivedLowerShriekCongrIso Λ e).inv = (rightDerivedLowerShriekCongrIso Λ e.symm).hom := by
  subst e
  rfl

lemma rightDerivedLowerShriekCongrIso_hom_app_self {X Y : Scheme.{u}} {f : X ⟶ Y}
    [HasCompactification f] (e : f = f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekCongrIso Λ e).hom.app K = 𝟙 _ :=
  rfl

variable [Finite Λ]

/-- The compact-support base change maps of two squares with equal sides agree up to the
congruence isomorphisms of the lower shriek. -/
lemma rightDerivedLowerShriekBaseChangeMap_app_congr {X X' Y Y' : Scheme.{u}} {v : Y' ⟶ Y}
    {v' : X' ⟶ X} {f₁ f₂ : X ⟶ Y} {f₁' f₂' : X' ⟶ Y'} [HasCompactification f₁]
    [HasCompactification f₂] [HasCompactification f₁'] [HasCompactification f₂']
    [QuasiCompact f₁'] [QuasiCompact f₂'] (e : f₁ = f₂) (e' : f₁' = f₂')
    (sq₁ : IsPullback v' f₁' f₁ v) (sq₂ : IsPullback v' f₂' f₂ v)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekBaseChangeMap Λ sq₁).app K ≫
        (rightDerivedLowerShriekCongrIso Λ e').hom.app ((L((v')^*[ModuleCat.{u + 1} Λ])).obj K) =
      (L((v)^*[ModuleCat.{u + 1} Λ])).map ((rightDerivedLowerShriekCongrIso Λ e).hom.app K) ≫
        (rightDerivedLowerShriekBaseChangeMap Λ sq₂).app K := by
  subst e e'
  simp only [rightDerivedLowerShriekCongrIso_hom_app_self, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact Category.comp_id _

end Congr

/-- Naturality of `ι` along `f`, in a form avoiding a comparison of components of `ι` at
definitionally equal objects. -/
lemma comp_map_eq_of_naturality {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (ι : F ⟶ G) {P Q : C} (f : P ⟶ Q) {A : D} (e : A ⟶ F.obj P) (η : A ⟶ G.obj P)
    (hη : e ≫ ι.app P = η) (r : A ⟶ F.obj Q) (hr : e ≫ F.map f = r) :
    η ≫ G.map f = r ≫ ι.app Q := by
  rw [← hη, Category.assoc, ← ι.naturality, ← reassoc_of% hr]

variable [Finite Λ] {X X' s s' : Scheme.{u}} {g : X' ⟶ X} {h : s' ⟶ s} {a : X ⟶ s}
  {a' : X' ⟶ s'} [QuasiCompact a] [HasCompactification a] [QuasiCompact a']
  [HasCompactification a']

omit [QuasiCompact a'] [HasCompactification a'] in
/-- The compact-support base change of the square `g ≫ (a ≫ 𝟙) = (a' ≫ h) ≫ 𝟙`, for an
isomorphism `g`, is, through `L(𝟙)^* ≅ 𝟭` and the congruence `a ≫ 𝟙 = a`, the pullback
`Ra_! ⟶ Ra_! Rg_* Lg^* ≅ Ra_! Rg_! Lg^* ≅ R(g ≫ a)_! Lg^* = R(a' ≫ h)_! Lg^*` along `g`. -/
lemma rightDerivedLowerShriekBaseChangeMap_app_eq_of_isIso_top [IsIso g]
    (sq : IsPullback g a' a h) [HasCompactification (a' ≫ h)] [QuasiCompact (a' ≫ h)]
    [HasCompactification (a ≫ 𝟙 s)] [QuasiCompact (a ≫ 𝟙 s)] [HasCompactification (g ≫ a)]
    [QuasiCompact (g ≫ a)]
    (sq' : IsPullback g (a' ≫ h) (a ≫ 𝟙 s) (𝟙 s))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((𝟙 s)^*[ModuleCat.{u + 1} Λ])).map
        ((rightDerivedLowerShriekCongrIso Λ (Category.comp_id a)).inv.app K) ≫
      (rightDerivedLowerShriekBaseChangeMap Λ sq').app K =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) s).hom.app
          ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) ≫
        (R(a)_![ModuleCat.{u + 1} Λ]).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app K) ≫
        (R(a)_![ModuleCat.{u + 1} Λ]).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) g).inv.app
            ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
        (rightDerivedLowerShriekCompIso Λ g a).inv.app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
        (rightDerivedLowerShriekCongrIso Λ sq.w).hom.app
          ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) := by
  have : HasCompactification (𝟙 X ≫ a) := HasCompactification.of_eq (Category.id_comp a).symm
  have : QuasiCompact (𝟙 X ≫ a) := by rw [Category.id_comp]; infer_instance
  -- the stacked squares `g ≫ 𝟙 = g ≫ 𝟙` and `𝟙 ≫ a = a ≫ 𝟙`
  have sqf : IsPullback g g (𝟙 X) (𝟙 X) := IsPullback.of_vert_isIso ⟨rfl⟩
  have sqg : IsPullback (𝟙 X) a a (𝟙 s) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have sqgf := sqf.paste_vert sqg
  have hP := rightDerivedLowerShriekBaseChangeMap_paste_vert (Λ := Λ) sqf sqg sqgf K
  have hc := rightDerivedLowerShriekBaseChangeMap_app_congr Λ
    ((Category.comp_id a).trans (Category.id_comp a).symm) sq.w.symm sq' sqgf K
  -- solved forms of the inputs
  have h₁ (N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      (rightDerivedLowerShriekBaseChangeMap Λ sqg).app N =
        (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) s).hom.app
            ((R(a)_![ModuleCat.{u + 1} Λ]).obj N) ≫
          (R(a)_![ModuleCat.{u + 1} Λ]).map
            ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).inv.app N) := by
    rw [← leftDerivedUpperStarId_inv_app_comp_rightDerivedLowerShriekBaseChangeMap_app Λ sqg N, Iso.hom_inv_id_app_assoc]
  have h₃ : (rightDerivedLowerShriekBaseChangeMap Λ sqf).app K =
      (L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X).hom.app K) ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K ≫
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app K ≫
          (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) g).inv.app
            ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) := by
    have hu := rightDerivedLowerShriekBaseChangeMap_app_comp_eq_unit_app Λ g sqf K
    simp only [← Category.assoc] at hu ⊢
    rw [← hu, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have hI : (rightDerivedLowerShriekCongrIso Λ (Category.comp_id a)).inv.app K ≫
      (rightDerivedLowerShriekCongrIso Λ
        ((Category.comp_id a).trans (Category.id_comp a).symm)).hom.app K ≫
      (unboundedEtaleLowerShriekCompIso Λ (𝟙 X) a).inv.app K =
      (R(a)_![ModuleCat.{u + 1} Λ]).map
        ((rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X).inv.app K) := by
    have h₂ := rightDerivedLowerShriekCompIso_id_left_hom_app Λ a K
    rw [rightDerivedLowerShriekCompIso_eq_symm, Iso.symm_hom] at h₂
    have h₂' : (unboundedEtaleLowerShriekCompIso Λ (𝟙 X) a).inv.app K =
        (rightDerivedLowerShriekCongrIso Λ (Category.id_comp a)).hom.app K ≫
          (R(a)_![ModuleCat.{u + 1} Λ]).map
            ((rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X).inv.app K) := by
      rw [← h₂, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id]
      exact (Category.comp_id _).symm
    rw [h₂', rightDerivedLowerShriekCongrIso_inv, rightDerivedLowerShriekCongrIso_hom_app_trans_assoc,
      rightDerivedLowerShriekCongrIso_hom_app_trans_assoc, rightDerivedLowerShriekCongrIso_hom_app_self]
    exact Category.id_comp _
  have hJ : (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X).inv.app K ≫
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).inv.app
        ((R(𝟙 X)_![ModuleCat.{u + 1} Λ]).obj K) ≫
      (L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X).hom.app K) ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K = 𝟙 _ := by
    have hn := (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).inv.naturality
      ((rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X).hom.app K)
    dsimp only [Functor.id_map] at hn
    rw [← reassoc_of% hn, Iso.inv_hom_id_app_assoc]
    exact Iso.inv_hom_id_app _ _
  have hA : (rightDerivedLowerShriekBaseChangeMap Λ sq').app K =
      (L((𝟙 s)^*[ModuleCat.{u + 1} Λ])).map ((rightDerivedLowerShriekCongrIso Λ
          ((Category.comp_id a).trans (Category.id_comp a).symm)).hom.app K) ≫
        (rightDerivedLowerShriekBaseChangeMap Λ sqgf).app K ≫
        (rightDerivedLowerShriekCongrIso Λ sq.w).hom.app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) := by
    rw [← reassoc_of% hc, rightDerivedLowerShriekCongrIso_hom_app_trans,
      rightDerivedLowerShriekCongrIso_hom_app_self]
    exact (Category.comp_id _).symm
  have hB : (rightDerivedLowerShriekBaseChangeMap Λ sqgf).app K =
      (L((𝟙 s)^*[ModuleCat.{u + 1} Λ])).map
          ((unboundedEtaleLowerShriekCompIso Λ (𝟙 X) a).inv.app K) ≫
        (rightDerivedLowerShriekBaseChangeMap Λ sqg).app ((R(𝟙 X)_![ModuleCat.{u + 1} Λ]).obj K) ≫
        (R(a)_![ModuleCat.{u + 1} Λ]).map ((rightDerivedLowerShriekBaseChangeMap Λ sqf).app K) ≫
        (unboundedEtaleLowerShriekCompIso Λ g a).hom.app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) := by
    rw [← hP, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id]
    exact (Category.id_comp _).symm
  have hI' := congrArg (L((𝟙 s)^*[ModuleCat.{u + 1} Λ])).map hI
  simp only [Functor.map_comp] at hI'
  have hJ' := congrArg (R(a)_![ModuleCat.{u + 1} Λ]).map hJ
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id] at hJ'
  have hn := (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) s).hom.naturality
    ((R(a)_![ModuleCat.{u + 1} Λ]).map
      ((rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X).inv.app K))
  have hc' : (unboundedEtaleLowerShriekCompIso Λ g a).hom =
      (rightDerivedLowerShriekCompIso Λ g a).inv := by
    rw [rightDerivedLowerShriekCompIso_eq_symm]
    rfl
  rw [hA, hB]
  simp only [Category.assoc]
  rw [reassoc_of% hI', h₁]
  simp only [Category.assoc]
  rw [reassoc_of% hn, h₃, hc']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hJ']

/-- **The compact-support base change along a square of isomorphisms is the adjunct of the
composition isomorphism**: for a cartesian square `g ≫ a = a' ≫ h` with `g` and `h`
isomorphisms, `Ex_! : Lh^* Ra_! ⟶ Ra'_! Lg^*` is adjoint, under `Lh^* ⊣ Rh_*`, to
```
Ra_! ⟶ Ra_! Rg_* Lg^* ≅ Ra_! Rg_! Lg^* ≅ R(g ≫ a)_! Lg^* = R(a' ≫ h)_! Lg^* ≅ Rh_! Ra'_! Lg^*
  ≅ Rh_* Ra'_! Lg^*.
``` -/
theorem unit_app_comp_map_rightDerivedLowerShriekBaseChangeMap_app [IsIso g] [IsIso h]
    (sq : IsPullback g a' a h) [HasCompactification (a' ≫ h)] [QuasiCompact (a' ≫ h)]
    [HasCompactification (g ≫ a)] [QuasiCompact (g ≫ a)]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app
        ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) ≫
      (R((h)_*[ModuleCat.{u + 1} Λ])).map ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K) =
      (R(a)_![ModuleCat.{u + 1} Λ]).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app K) ≫
        (R(a)_![ModuleCat.{u + 1} Λ]).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) g).inv.app
            ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
        (rightDerivedLowerShriekCompIso Λ g a).inv.app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
        (rightDerivedLowerShriekCongrIso Λ sq.w).hom.app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
        (rightDerivedLowerShriekCompIso Λ a' h).hom.app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) h).hom.app
          ((R(a')_![ModuleCat.{u + 1} Λ]).obj ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  have : HasCompactification (a ≫ 𝟙 s) := HasCompactification.of_eq (Category.comp_id a).symm
  have : QuasiCompact (a ≫ 𝟙 s) := by rw [Category.comp_id]; infer_instance
  -- the square `sq` stacked on the square `h ≫ 𝟙 = h ≫ 𝟙`
  have sqg : IsPullback h h (𝟙 s) (𝟙 s) := IsPullback.of_vert_isIso ⟨rfl⟩
  have sqgf := sq.paste_vert sqg
  have hP := rightDerivedLowerShriekBaseChangeMap_paste_vert (Λ := Λ) sq sqg sqgf K
  have hL := rightDerivedLowerShriekBaseChangeMap_app_eq_of_isIso_top Λ sq sqgf K
  have hη (N : DerivedCategory (Sheaf s.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) s).inv.app N ≫
        (L((𝟙 s)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) s).inv.app N) ≫
        (rightDerivedLowerShriekBaseChangeMap Λ sqg).app N ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) h).hom.app
          ((L((h)^*[ModuleCat.{u + 1} Λ])).obj N) =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app N := by
    rw [rightDerivedLowerShriekBaseChangeMap_app_comp_eq_unit_app Λ h sqg N, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact Iso.inv_hom_id_app_assoc _ _ _
  have hK : (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) s).inv.app
        ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) ≫
      (unboundedEtaleLowerShriekCompIso Λ a (𝟙 s)).hom.app K =
      (rightDerivedLowerShriekCongrIso Λ (Category.comp_id a)).inv.app K := by
    have h₂ := rightDerivedLowerShriekCompIso_id_right_hom_app Λ a K
    rw [rightDerivedLowerShriekCompIso_eq_symm, Iso.symm_hom] at h₂
    rw [← cancel_mono ((rightDerivedLowerShriekCongrIso Λ (Category.comp_id a)).hom.app K),
      Iso.inv_hom_id_app, ← h₂, Category.assoc, Iso.hom_inv_id_app_assoc]
    exact Iso.inv_hom_id_app _ _
  have hι := (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) h).hom.naturality
    ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K)
  have hP' : (rightDerivedLowerShriekBaseChangeMap Λ sqg).app ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) ≫
      (R(h)_![ModuleCat.{u + 1} Λ]).map ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K) =
      (L((𝟙 s)^*[ModuleCat.{u + 1} Λ])).map
          ((unboundedEtaleLowerShriekCompIso Λ a (𝟙 s)).hom.app K) ≫
        (rightDerivedLowerShriekBaseChangeMap Λ sqgf).app K ≫
        (unboundedEtaleLowerShriekCompIso Λ a' h).inv.app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) := by
    rw [reassoc_of% hP, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have hc' : (unboundedEtaleLowerShriekCompIso Λ a' h).inv =
      (rightDerivedLowerShriekCompIso Λ a' h).hom := by
    rw [rightDerivedLowerShriekCompIso_eq_symm]
    rfl
  have key := comp_map_eq_of_naturality
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) h).hom
    (P := (L((h)^*[ModuleCat.{u + 1} Λ])).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K))
    (Q := (R(a')_![ModuleCat.{u + 1} Λ]).obj ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K))
    ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K)
    ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) s).inv.app ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) ≫
      (L((𝟙 s)^*[ModuleCat.{u + 1} Λ])).map
        ((rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) s).inv.app
          ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)) ≫
      (rightDerivedLowerShriekBaseChangeMap Λ sqg).app ((R(a)_![ModuleCat.{u + 1} Λ]).obj K))
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app
      ((R(a)_![ModuleCat.{u + 1} Λ]).obj K))
    (by simp only [Category.assoc]; exact hη _)
    ((R(a)_![ModuleCat.{u + 1} Λ]).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app K) ≫
      (R(a)_![ModuleCat.{u + 1} Λ]).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) g).inv.app
          ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
      (rightDerivedLowerShriekCompIso Λ g a).inv.app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
      (rightDerivedLowerShriekCongrIso Λ sq.w).hom.app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
      (rightDerivedLowerShriekCompIso Λ a' h).hom.app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K))
    (by
      simp only [Category.assoc]
      rw [hP', ← Functor.map_comp_assoc, hK, reassoc_of% hL, hc']
      exact Iso.inv_hom_id_app_assoc _ _ _)
  simpa only [Category.assoc] using key

end AlgebraicGeometry.Etale
