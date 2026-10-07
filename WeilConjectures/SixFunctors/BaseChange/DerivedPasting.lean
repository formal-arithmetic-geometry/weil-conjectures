/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Pasting
public import WeilConjectures.SixFunctors.BaseChange.Derived

/-!
# Pasting laws for the derived base change map and composition of `IsBaseChangeIso`

The derived base change map `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus` satisfies the
same pasting laws as the underived one (`WeilConjectures.SixFunctors.BaseChange.Pasting`).
For two squares pasted vertically

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
  |          |
  e'         e
  ↓          ↓
  Z' --k---> Z
```

the derived base change map of the pasted square is the composite
`k^* R(f ≫ e)_* ≅ k^* Re_* Rf_* ⟶ Re'_* g^* Rf_* ⟶ Re'_* Rf'_* g'^* ≅ R(f' ≫ e')_* g'^*` of the
derived base change maps of the two squares, modulo the composition isomorphisms
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso'` of the derived pushforwards
(`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_vert`). The proof is by the
uniqueness principle `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_ext`: both sides are
computed on bounded below complexes by the underived base change maps, and the underived
pasting law `AlgebraicGeometry.Etale.baseChangeMap_paste_vert` identifies the results. The
horizontal pasting law `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_horiz` (modulo
the composition isomorphisms `AlgebraicGeometry.Etale.upperStarCompDerivedPlus` of the derived
pullbacks) is proved in the same way.

As a consequence, the proper base change property is stable under composition: if `f` and `e`
satisfy `AlgebraicGeometry.Etale.IsBaseChangeIso`, so does `f ≫ e`
(`AlgebraicGeometry.Etale.IsBaseChangeIso.comp`), since every cartesian square on `f ≫ e`
is the vertical pasting of cartesian squares on `e` and on `f`
(`CategoryTheory.IsPullback.paste_vert`).
(blueprint: `lemma:weil-pbc-derived-exchange-coherence`, vertical pasting;
`lemma:weil-pbc-composition`, formal part)

For the identity square on `f` the derived base change map is the identity, modulo the identity
isomorphisms of the derived pullbacks (`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_id`);
with the horizontal pasting law this is blueprint `sbc-lem-identity-and-base-change-composition`.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace CategoryTheory.NatTrans

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Preadditive C] [Preadditive D] [Preadditive E]

/-- `NatTrans.mapHomotopyCategoryPlus` is compatible with right whiskering, definitionally. -/
lemma mapHomotopyCategoryPlus_whiskerRight_app {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) (H : D ⥤ E) [H.Additive] (K : HomotopyCategory.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerRight α H)).app K =
      H.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus α).app K) :=
  rfl

/-- `NatTrans.mapHomotopyCategoryPlus` is compatible with left whiskering, definitionally. -/
lemma mapHomotopyCategoryPlus_whiskerLeft_app (F : C ⥤ D) [F.Additive] {G H : D ⥤ E}
    [G.Additive] [H.Additive] (α : G ⟶ H) (K : HomotopyCategory.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerLeft F α)).app K =
      (NatTrans.mapHomotopyCategoryPlus α).app (F.mapHomotopyCategoryPlus.obj K) :=
  rfl

end CategoryTheory.NatTrans

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

open Etale

section Instances

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pushforward `f_*` preserves injective objects, being right adjoint to the exact
functor `f^*`. -/
instance Etale.preservesInjectiveObjects_lowerStar : ((f)_*[A]).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Etale.upperStarLowerStarAdjunction A f)

end Instances

section Vertical

variable {X' X Y' Y Z' Z : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {k : Z' ⟶ Z}

/-- The underived vertical pasting law, without associators. -/
lemma Etale.baseChangeMap_paste_vert' (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g e' e k)
    (sq : CommSq g' (f' ≫ e') (f ≫ e) k) :
    Etale.baseChangeMap A sq =
      Functor.whiskerRight (Etale.lowerStarComp A f e).inv ((k)^*[A]) ≫
        Functor.whiskerLeft ((f)_*[A]) (Etale.baseChangeMap A sq₂) ≫
        Functor.whiskerRight (Etale.baseChangeMap A sq₁) ((e')_*[A]) ≫
        Functor.whiskerLeft ((g')^*[A]) (Etale.lowerStarComp A f' e').hom := by
  refine NatTrans.ext (funext fun F => ?_)
  rw [Etale.baseChangeMap_paste_vert_app A sq₁ sq₂ sq]
  rfl

/-- **Vertical pasting of the derived base change maps**: for two squares pasted vertically,
the derived base change map of the pasted square is the composite
`k^* R(f ≫ e)_* ≅ k^* Re_* Rf_* ⟶ Re'_* g^* Rf_* ⟶ Re'_* Rf'_* g'^* ≅ R(f' ≫ e')_* g'^*` of
the derived base change maps of the two squares, modulo the composition isomorphisms of the
derived pushforwards along the vertical maps. -/
lemma Etale.derivedBaseChangeMapPlus_paste_vert (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g e' e k) (sq : CommSq g' (f' ≫ e') (f ≫ e) k) :
    Etale.derivedBaseChangeMapPlus A sq =
      Functor.whiskerRight (Functor.rightDerivedFunctorPlusCompIso' (f)_*[A] (e)_*[A]
          (Etale.lowerStarComp A f e)).inv ((k)^*[A]).mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (f)_*[A].rightDerivedFunctorPlus
          (Etale.derivedBaseChangeMapPlus A sq₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Etale.derivedBaseChangeMapPlus A sq₁)
          (e')_*[A].rightDerivedFunctorPlus ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((g')^*[A]).mapDerivedCategoryPlus
          (Functor.rightDerivedFunctorPlusCompIso' (f')_*[A] (e')_*[A]
            (Etale.lowerStarComp A f' e')).hom := by
  symm
  refine Etale.derivedBaseChangeMapPlus_ext A sq _ fun K => ?_
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj, id_comp]
  -- the unit of `R(f ≫ e)_*` through the composition isomorphism
  have hCI1 : (f ≫ e)_*[A].rightDerivedFunctorPlusUnit.app K ≫
      (Functor.rightDerivedFunctorPlusCompIso' (f)_*[A] (e)_*[A]
        (Etale.lowerStarComp A f e)).inv.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarComp A f e).inv).app K) ≫
        (e)_*[A].rightDerivedFunctorPlusUnit.app ((f)_*[A].mapHomotopyCategoryPlus.obj K) ≫
        (e)_*[A].rightDerivedFunctorPlus.map ((f)_*[A].rightDerivedFunctorPlusUnit.app K) := by
    have h := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac (f)_*[A] (e)_*[A]
      (Etale.lowerStarComp A f e)) K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_obj, Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc] at h
    have h' : (f ≫ e)_*[A].rightDerivedFunctorPlusUnit.app K =
        DerivedCategory.Plus.Qh.map
            ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarComp A f e).inv).app K) ≫
          (e)_*[A].rightDerivedFunctorPlusUnit.app ((f)_*[A].mapHomotopyCategoryPlus.obj K) ≫
          (e)_*[A].rightDerivedFunctorPlus.map ((f)_*[A].rightDerivedFunctorPlusUnit.app K) ≫
          (Functor.rightDerivedFunctorPlusCompIso' (f)_*[A] (e)_*[A]
            (Etale.lowerStarComp A f e)).hom.app (DerivedCategory.Plus.Qh.obj K) := by
      rw [h, ← Category.assoc, ← DerivedCategory.Plus.Qh.map_comp, ← NatTrans.comp_app,
        ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.inv_hom_id,
        NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app, DerivedCategory.Plus.Qh.map_id,
        Category.id_comp]
    rw [h']
    simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
  -- naturality of the derived base change map of the lower square along the unit of `Rf_*`
  have hnat₂ := (Etale.derivedBaseChangeMapPlus A sq₂).naturality
    ((f)_*[A].rightDerivedFunctorPlusUnit.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hnat₂
  have hfac₂ := Etale.derivedBaseChangeMapPlus_fac_app A sq₂
    ((f)_*[A].mapHomotopyCategoryPlus.obj K)
  have hfac₁ := Etale.derivedBaseChangeMapPlus_fac_app A sq₁ K
  have hnatη : DerivedCategory.Plus.Qh.map (((e')_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₁)).app K)) ≫
      (e')_*[A].rightDerivedFunctorPlusUnit.app
        ((f')_*[A].mapHomotopyCategoryPlus.obj (((g')^*[A]).mapHomotopyCategoryPlus.obj K)) =
      (e')_*[A].rightDerivedFunctorPlusUnit.app
        (((g)^*[A]).mapHomotopyCategoryPlus.obj ((f)_*[A].mapHomotopyCategoryPlus.obj K)) ≫
      (e')_*[A].rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₁)).app K)) :=
    (e')_*[A].rightDerivedFunctorPlusUnit.naturality
      ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₁)).app K)
  have hCI2 := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac (f')_*[A]
    (e')_*[A] (Etale.lowerStarComp A f' e')) (((g')^*[A]).mapHomotopyCategoryPlus.obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc] at hCI2
  have hnatCI := (Functor.rightDerivedFunctorPlusCompIso' (f')_*[A] (e')_*[A]
    (Etale.lowerStarComp A f' e')).hom.naturality
    (((g')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hnatCI
  have hnatF : ((k)^*[A]).mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarComp A f e).inv).app K)) ≫
      ((k)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        ((e)_*[A].mapHomotopyCategoryPlus.obj ((f)_*[A].mapHomotopyCategoryPlus.obj K)) =
      ((k)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        ((f ≫ e)_*[A].mapHomotopyCategoryPlus.obj K) ≫
      DerivedCategory.Plus.Qh.map (((k)^*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarComp A f e).inv).app K)) :=
    ((k)^*[A]).mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarComp A f e).inv).app K)
  have hpaste : (NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq)).app K =
      ((k)^*[A]).mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarComp A f e).inv).app K) ≫
        (NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₂)).app
          ((f)_*[A].mapHomotopyCategoryPlus.obj K) ≫
        ((e')_*[A]).mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₁)).app K) ≫
        (NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarComp A f' e').hom).app
          (((g')^*[A]).mapHomotopyCategoryPlus.obj K) := by
    rw [Etale.baseChangeMap_paste_vert' A sq₁ sq₂ sq, NatTrans.mapHomotopyCategoryPlus_comp,
      NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.mapHomotopyCategoryPlus_comp,
      NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app]
    rfl
  rw [← Functor.map_comp_assoc, hCI1, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, reassoc_of% hnat₂, reassoc_of% hfac₂, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, Category.assoc, hfac₁, Iso.inv_hom_id_app_assoc,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, ← reassoc_of% hnatη,
    hnatCI, reassoc_of% hCI2, reassoc_of% hnatF, hpaste, Functor.map_comp,
    Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]

/-- If the derived base change maps of two squares pasted vertically are isomorphisms, so is
the derived base change map of the pasted square (whose left vertical map is only required
to be equal to the composite). -/
lemma Etale.isIso_derivedBaseChangeMapPlus_of_paste_vert {f'' : X' ⟶ Z'}
    (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g e' e k) (sq : CommSq g' f'' (f ≫ e) k)
    (hf'' : f'' = f' ≫ e') [IsIso (Etale.derivedBaseChangeMapPlus A sq₁)]
    [IsIso (Etale.derivedBaseChangeMapPlus A sq₂)] :
    IsIso (Etale.derivedBaseChangeMapPlus A sq) := by
  subst hf''
  rw [Etale.derivedBaseChangeMapPlus_paste_vert A sq₁ sq₂ sq]
  infer_instance

end Vertical

section Horizontal

variable {X'' X' X Y'' Y' Y : Scheme.{u}} {g'' : X'' ⟶ X'} {g' : X' ⟶ X} {f'' : X'' ⟶ Y''}
  {f' : X' ⟶ Y'} {f : X ⟶ Y} {h : Y'' ⟶ Y'} {g : Y' ⟶ Y}

/-- The underived horizontal pasting law, without associators. -/
lemma Etale.baseChangeMap_paste_horiz' (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g'' f'' f' h)
    (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)) :
    Etale.baseChangeMap A sq =
      Functor.whiskerLeft ((f)_*[A]) (Etale.upperStarComp A h g).hom ≫
        Functor.whiskerRight (Etale.baseChangeMap A sq₁) ((h)^*[A]) ≫
        Functor.whiskerLeft ((g')^*[A]) (Etale.baseChangeMap A sq₂) ≫
        Functor.whiskerRight (Etale.upperStarComp A g'' g').inv ((f'')_*[A]) := by
  refine NatTrans.ext (funext fun F => ?_)
  rw [Etale.baseChangeMap_paste_horiz_app A sq₁ sq₂ sq]
  rfl

set_option maxHeartbeats 800000 in
-- the proof is a long chain of rewrites in the bounded below derived categories, each of
-- which is cheap but the heartbeat count is per declaration
/-- **Horizontal pasting of the derived base change maps**: for two squares pasted
horizontally, the derived base change map of the pasted square is the composite
`(h ≫ g)^* Rf_* ≅ h^* g^* Rf_* ⟶ h^* Rf'_* g'^* ⟶ Rf''_* g''^* g'^* ≅ Rf''_* (g'' ≫ g')^*` of
the derived base change maps of the two squares, modulo the composition isomorphisms
`AlgebraicGeometry.Etale.upperStarCompDerivedPlus` of the derived pullbacks along the
horizontal maps. -/
lemma Etale.derivedBaseChangeMapPlus_paste_horiz (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g'' f'' f' h) (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)) :
    Etale.derivedBaseChangeMapPlus A sq =
      Functor.whiskerLeft (f)_*[A].rightDerivedFunctorPlus
          (Etale.upperStarCompDerivedPlus A h g).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Etale.derivedBaseChangeMapPlus A sq₁)
          ((h)^*[A]).mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((g')^*[A]).mapDerivedCategoryPlus
          (Etale.derivedBaseChangeMapPlus A sq₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Etale.upperStarCompDerivedPlus A g'' g').inv
          (f'')_*[A].rightDerivedFunctorPlus := by
  -- it suffices to prove the equation after composing with the composition isomorphism
  suffices hmain : Etale.derivedBaseChangeMapPlus A sq ≫
      Functor.whiskerRight (Etale.upperStarCompDerivedPlus A g'' g').hom
        (f'')_*[A].rightDerivedFunctorPlus =
      Functor.whiskerLeft (f)_*[A].rightDerivedFunctorPlus
          (Etale.upperStarCompDerivedPlus A h g).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Etale.derivedBaseChangeMapPlus A sq₁)
          ((h)^*[A]).mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((g')^*[A]).mapDerivedCategoryPlus
          (Etale.derivedBaseChangeMapPlus A sq₂) ≫
        (Functor.associator _ _ _).inv by
    rw [← cancel_mono (Functor.whiskerRight (Etale.upperStarCompDerivedPlus A g'' g').hom
      (f'')_*[A].rightDerivedFunctorPlus), hmain]
    simp only [Category.assoc, ← Functor.whiskerRight_comp, Iso.inv_hom_id,
      Functor.whiskerRight_id', Category.comp_id]
  refine Functor.rightDerived_ext _ (Etale.rightDerivedLowerStarPlusCompUpperStarUnit A f (h ≫ g))
    (HomotopyCategory.Plus.quasiIso _) _ _ _ (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj, id_comp,
    Etale.rightDerivedLowerStarPlusCompUpperStarUnit, comp_id]
  -- the left hand side: the characterisation of the derived base change map of `sq`
  rw [Etale.derivedBaseChangeMapPlus_fac_app_assoc A sq K]
  have hfac₁ := Etale.derivedBaseChangeMapPlus_fac_app A sq₁ K
  have hfac₂ := Etale.derivedBaseChangeMapPlus_fac_app A sq₂
    (((g')^*[A]).mapHomotopyCategoryPlus.obj K)
  -- naturality of the composition isomorphism along the unit of `Rf_*`
  have hnatC := (Etale.upperStarCompDerivedPlus A h g).hom.naturality
    ((f)_*[A].rightDerivedFunctorPlusUnit.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hnatC
  -- naturality of the derived base change map of the right square along `factorsh`
  have hnat₂ : ((h)^*[A]).mapDerivedCategoryPlus.map ((f')_*[A].rightDerivedFunctorPlus.map
        (((g')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app K)) ≫
      (Etale.derivedBaseChangeMapPlus A sq₂).app
        (((g')^*[A]).mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      (Etale.derivedBaseChangeMapPlus A sq₂).app
        (DerivedCategory.Plus.Qh.obj (((g')^*[A]).mapHomotopyCategoryPlus.obj K)) ≫
      (f'')_*[A].rightDerivedFunctorPlus.map (((g'')^*[A]).mapDerivedCategoryPlus.map
        (((g')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app K)) :=
    (Etale.derivedBaseChangeMapPlus A sq₂).naturality
      (((g')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app K)
  -- naturality of `factorsh` for `h^*` along the underived base change map of the left square
  have hnatF : ((h)^*[A]).mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₁)).app K)) ≫
      ((h)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        ((f')_*[A].mapHomotopyCategoryPlus.obj (((g')^*[A]).mapHomotopyCategoryPlus.obj K)) =
      ((h)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        (((g)^*[A]).mapHomotopyCategoryPlus.obj ((f)_*[A].mapHomotopyCategoryPlus.obj K)) ≫
      DerivedCategory.Plus.Qh.map (((h)^*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₁)).app K)) :=
    ((h)^*[A]).mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₁)).app K)
  have hC₁ := Etale.upperStarCompDerivedPlus_hom_app_factorsh A h g (h ≫ g) rfl
    ((f)_*[A].mapHomotopyCategoryPlus.obj K)
  have hC₂ := Etale.upperStarCompDerivedPlus_hom_app_factorsh A g'' g' (g'' ≫ g') rfl K
  -- the composition isomorphism on the right, rearranged
  have hC₂' : ((g'' ≫ g')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app K ≫
      (Etale.upperStarCompDerivedPlus A g'' g').hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (Etale.upperStarComp A g'' g').hom).app K) ≫
        ((g'')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app
          (((g')^*[A]).mapHomotopyCategoryPlus.obj K) ≫
        ((g'')^*[A]).mapDerivedCategoryPlus.map
          (((g')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app K) := by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, ← Category.assoc, ← Category.assoc, ← hC₂]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.id_comp, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.comp_id]
  have hpaste : (NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq)).app K =
      (NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A h g).hom).app
          ((f)_*[A].mapHomotopyCategoryPlus.obj K) ≫
        ((h)^*[A]).mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₁)).app K) ≫
        (NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₂)).app
          (((g')^*[A]).mapHomotopyCategoryPlus.obj K) ≫
        ((f'')_*[A]).mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g'' g').inv).app K) := by
    rw [Etale.baseChangeMap_paste_horiz' A sq₁ sq₂ sq, NatTrans.mapHomotopyCategoryPlus_comp,
      NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.mapHomotopyCategoryPlus_comp,
      NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app]
    rfl
  have hη : DerivedCategory.Plus.Qh.map (((f'')_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g'' g').hom).app K)) ≫
      (f'')_*[A].rightDerivedFunctorPlusUnit.app
        (((g'')^*[A]).mapHomotopyCategoryPlus.obj (((g')^*[A]).mapHomotopyCategoryPlus.obj K)) =
      (f'')_*[A].rightDerivedFunctorPlusUnit.app (((g'' ≫ g')^*[A]).mapHomotopyCategoryPlus.obj K) ≫
      (f'')_*[A].rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g'' g').hom).app K)) :=
    (f'')_*[A].rightDerivedFunctorPlusUnit.naturality
      ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g'' g').hom).app K)
  have hcancel : ((f'')_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g'' g').inv).app K) ≫
      ((f'')_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g'' g').hom).app K) = 𝟙 _ := by
    rw [← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp,
      Iso.inv_hom_id, NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app,
      CategoryTheory.Functor.map_id]
  -- `rw` is avoided below where its unifier would unfold the derived functors: `simp only`
  -- works up to reducible transparency and is fast here.
  -- the right hand side: expand the left square and push the base change map of the right
  -- square through `factorsh`
  rw [reassoc_of% hnatC, ← Functor.map_comp_assoc, hfac₁, Functor.map_comp, Functor.map_comp,
    Functor.map_comp]
  simp only [Category.assoc]
  simp only [hnat₂, reassoc_of% hfac₂, reassoc_of% hnatF, reassoc_of% hC₁]
  -- the left hand side: rearrange the composition isomorphism and use the underived pasting
  have hc2 : DerivedCategory.Plus.Qh.map (((f'')_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g'' g').inv).app K)) ≫
      DerivedCategory.Plus.Qh.map (((f'')_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g'' g').hom).app K)) = 𝟙 _ := by
    rw [← DerivedCategory.Plus.Qh.map_comp, hcancel, DerivedCategory.Plus.Qh.map_id]
  simp only [← Functor.map_comp]
  simp only [hC₂']
  simp only [Functor.map_comp]
  simp only [← reassoc_of% hη, hpaste, Functor.map_comp, Category.assoc, reassoc_of% hc2]

end Horizontal

section Identity

variable {X Y : Scheme.{u}}

omit [HasSmallSiteSheafify A] in
/-- The composition isomorphism `AlgebraicGeometry.Etale.upperStarComp` along two equal
diagonals `d = d'` agree up to the induced identification of the pullbacks. -/
lemma Etale.upperStarComp_congr {T S R : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) (d d' : T ⟶ R)
    (hd : d = h₁ ≫ h₂) (hd' : d' = h₁ ≫ h₂) (h : d = d') :
    Etale.upperStarComp A h₁ h₂ d hd =
      eqToIso (by rw [h]) ≪≫ Etale.upperStarComp A h₁ h₂ d' hd' := by
  subst h
  simp

omit [HasSmallSiteSheafify A] in
/-- The square isomorphism of the identity square on `f` is built from the identity
isomorphisms `(𝟙 _)^* ≅ 𝟭`. -/
lemma Etale.squareUpperStarIso_id (f : X ⟶ Y) (sq : CommSq (𝟙 X) f f (𝟙 Y)) :
    Etale.squareUpperStarIso A sq =
      Functor.isoWhiskerRight (Etale.upperStarId A Y) (f)^*[A] ≪≫ Functor.leftUnitor _ ≪≫
        (Functor.rightUnitor _).symm ≪≫
          Functor.isoWhiskerLeft (f)^*[A] (Etale.upperStarId A X).symm := by
  rw [Etale.squareUpperStarIso, Etale.upperStarComp_congr A f (𝟙 Y) _ f sq.w
      (Category.comp_id f).symm (Category.id_comp f),
    Etale.upperStarComp_congr A (𝟙 X) f _ f rfl (Category.id_comp f).symm (Category.id_comp f),
    Etale.upperStarComp_id_left, Etale.upperStarComp_id_right]
  ext M
  simp

omit [HasSmallSiteSheafify A] in
/-- **The underived base change map of the identity square** is the identity, modulo the
identity isomorphisms `(𝟙 _)^* ≅ 𝟭` of the pullbacks. -/
lemma Etale.baseChangeMap_id (f : X ⟶ Y) (sq : CommSq (𝟙 X) f f (𝟙 Y)) :
    Etale.baseChangeMap A sq =
      Functor.whiskerLeft (f)_*[A] (Etale.upperStarId A Y).hom ≫ (Functor.rightUnitor _).hom ≫
        (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (Etale.upperStarId A X).inv (f)_*[A] := by
  ext F : 2
  simp only [Etale.baseChangeMap, Etale.squareUpperStarIso_id, mateEquiv_apply]
  simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.id_comp,
    Category.comp_id, Functor.map_comp, Category.assoc]
  have h₁ := (Etale.upperStarLowerStarAdjunction A f).unit.naturality
    ((Etale.upperStarId A Y).hom.app (((f)_*[A]).obj F))
  have h₂ := (Etale.upperStarId A X).inv.naturality
    ((Etale.upperStarLowerStarAdjunction A f).counit.app F)
  simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at h₁ h₂
  rw [← reassoc_of% h₁, Functor.comp_map, ← Functor.map_comp, ← h₂,
    Functor.map_comp, Adjunction.right_triangle_components_assoc]

/-- Blueprint `sbc-lem-identity-and-base-change-composition` (identity part): **the derived
exchange morphism of the identity square is the identity**, modulo the identity isomorphisms
`D(𝟙 _)^*⁺ ≅ 𝟭` of the derived pullbacks. The composition part of that blueprint lemma is the
horizontal pasting law `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_horiz`. -/
lemma Etale.derivedBaseChangeMapPlus_id (f : X ⟶ Y) (sq : CommSq (𝟙 X) f f (𝟙 Y)) :
    Etale.derivedBaseChangeMapPlus A sq =
      Functor.whiskerLeft (f)_*[A].rightDerivedFunctorPlus (Etale.upperStarIdDerivedPlus A Y).hom ≫
        (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (Etale.upperStarIdDerivedPlus A X).inv
          (f)_*[A].rightDerivedFunctorPlus := by
  symm
  refine Etale.derivedBaseChangeMapPlus_ext A sq _ fun K => ?_
  rw [Etale.baseChangeMap_id]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.id_comp,
    NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.mapHomotopyCategoryPlus_rightUnitor_hom_app,
    NatTrans.mapHomotopyCategoryPlus_leftUnitor_inv_app,
    NatTrans.mapHomotopyCategoryPlus_whiskerLeft_app,
    NatTrans.mapHomotopyCategoryPlus_whiskerRight_app, Functor.map_comp]
  have n₁ := (Etale.upperStarIdDerivedPlus A Y).hom.naturality
    ((f)_*[A].rightDerivedFunctorPlusUnit.app K)
  have e₁ := Etale.upperStarIdDerivedPlus_hom_app A Y ((f)_*[A].mapHomotopyCategoryPlus.obj K)
  have n₂ := (f)_*[A].rightDerivedFunctorPlusUnit.naturality
    ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A X).inv).app K)
  have e₂ : DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A X).inv).app K) ≫
      ((𝟙 X)^*[A]).mapDerivedCategoryPlusFactorsh.inv.app K =
      (Etale.upperStarIdDerivedPlus A X).inv.app (DerivedCategory.Plus.Qh.obj K) := by
    rw [← cancel_epi ((Etale.upperStarIdDerivedPlus A X).hom.app (DerivedCategory.Plus.Qh.obj K)),
      Iso.hom_inv_id_app,
      Etale.upperStarIdDerivedPlus_hom_app, Category.assoc, ← Functor.map_comp_assoc,
      ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.hom_inv_id,
      NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.hom_inv_id_app]
    rfl
  simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at n₁ n₂
  rw [reassoc_of% n₁, e₁]
  simp only [Category.assoc]
  erw [reassoc_of% n₂]
  rw [← Functor.map_comp, e₂]
  erw [Category.id_comp]
  rfl

end Identity

section Comp

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ⟶ Z)

/-- **The proper base change property is stable under composition**: if `f` and `e` satisfy
`AlgebraicGeometry.Etale.IsBaseChangeIso`, so does `f ≫ e`. Every cartesian square on `f ≫ e`
is the vertical pasting of the cartesian square on `e` with the same base change and the
induced cartesian square on `f`, and the derived base change maps paste accordingly.
(blueprint: `lemma:weil-pbc-composition`, formal part) -/
lemma Etale.IsBaseChangeIso.comp [Etale.IsBaseChangeIso A f] [Etale.IsBaseChangeIso A e] :
    Etale.IsBaseChangeIso A (f ≫ e) where
  isIso {X' Z'} g' f'' k sq := by
    let f' : X' ⟶ pullback e k := pullback.lift (g' ≫ f) f'' (by rw [Category.assoc, sq.w])
    have hf'' : f'' = f' ≫ pullback.snd e k := (pullback.lift_snd _ _ _).symm
    have sq₂ : IsPullback (pullback.fst e k) (pullback.snd e k) e k :=
      IsPullback.of_hasPullback e k
    have sq₁ : IsPullback g' f' f (pullback.fst e k) :=
      IsPullback.of_bot (hf'' ▸ sq) (pullback.lift_fst _ _ _).symm sq₂
    have h₁ := Etale.IsBaseChangeIso.isIso (A := A) g' f' (pullback.fst e k) sq₁
    have h₂ := Etale.IsBaseChangeIso.isIso (A := A) (pullback.fst e k) (pullback.snd e k) k sq₂
    exact Etale.isIso_derivedBaseChangeMapPlus_of_paste_vert A sq₁.toCommSq sq₂.toCommSq
      sq.toCommSq hf''

end Comp

end AlgebraicGeometry
