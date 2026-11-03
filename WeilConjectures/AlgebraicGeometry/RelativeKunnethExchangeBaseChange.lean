/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
import all WeilConjectures.AlgebraicGeometry.RelativeKunnethCompositorBaseChange
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Exchange pasting in arbitrary cartesian realizations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local instance] unbounded_has_base_change unbounded_has_proper_exchange

private theorem relativeKunneth_exact_exchange_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (sq₃ : IsPullback (w' ≫ v') f'' f (w ≫ v)) :
    unboundedEtaleCompactSupportBaseChange A sq₃ =
      Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
        (unboundedEtaleUpperStarCompIso A w v).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (unboundedEtaleCompactSupportBaseChange A sq₁)
        (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory
        (unboundedEtaleCompactSupportBaseChange A sq₂) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (unboundedEtaleUpperStarCompIso A w' v').inv
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'') := by
  have h := congrArg TwoSquare.natTrans
    (chosenBaseChange_paste_horiz (unboundedFormalism A) sq₁ sq₂ sq₃)
  have hc {S T U : Scheme.{u}} (a : S ⟶ T) (b : T ⟶ U) :
      (unboundedFormalism A).pbComp a b = unboundedEtaleUpperStarCompIso A a b := rfl
  rw [hc, hc] at h
  simp only [relativeKunneth_chosen_base_change_general, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.vComp, TwoSquare.mk, TwoSquare.natTrans] at h
  change (_ : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
      (upperStar (ModuleCat.{u + 1} A) (w ≫ v)).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) (w' ≫ v')).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'')) = _ at h
  simp only [Category.assoc] at h
  exact h

attribute [local irreducible] unboundedEtaleCompactSupportBaseChange

private theorem relativeKunneth_exchange_paste_aux (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (K : DerivedCategoryModule A X) :
    (L((w)^*[ModuleCat.{u + 1} A])).map ((rightDerivedLowerShriekBaseChangeMap A sq₁).app K) ≫
        (rightDerivedLowerShriekBaseChangeMap A sq₂).app
          ((L((v')^*[ModuleCat.{u + 1} A])).obj K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).inv.app _ ≫
        (rightDerivedLowerShriekBaseChangeMap A (sq₂.paste_horiz sq₁)).app K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'').map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').hom.app K) := by
  have h := congr_app (relativeKunneth_exact_exchange_comp A sq₁ sq₂
    (sq₂.paste_horiz sq₁)) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    unboundedEtaleCompactSupportBaseChange,
    unboundedEtaleUpperStarCompIso, Iso.trans_hom, Iso.trans_inv, Functor.map_comp,
    Category.assoc] at h
  apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).hom.app _)).mp
  apply (cancel_mono ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'').map
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').inv.app K))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  apply (cancel_epi ((leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) (w ≫ v)).inv.app _)).mp
  apply (cancel_mono ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'').map
    ((leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} A) (w' ≫ v')).hom.app K))).mp
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Category.assoc, Iso.inv_hom_id_app_assoc,
    Functor.map_comp]
  simp only [leftDerivedUpperStarIsoMapDerivedCategory, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, Category.comp_id] at h ⊢
  simp only [Category.id_comp]
  rw [h]
  simp only [Functor.map_comp]
  have hn :=
    (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctorIsoMapDerivedCategory.inv.naturality
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').map
      ((upperStar (ModuleCat.{u + 1} A) v').leftDerivedFunctorIsoMapDerivedCategory.hom.app K))
  rw [reassoc_of% hn]
  have he := (rightDerivedLowerShriekBaseChangeMap A sq₂).naturality
    ((upperStar (ModuleCat.{u + 1} A) v').leftDerivedFunctorIsoMapDerivedCategory.hom.app K)
  simp only [Functor.comp_map] at he
  rw [reassoc_of% he]
  rw [← Functor.map_comp_assoc]
  rw [← (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctorIsoMapDerivedCategory.hom.naturality]
  simp only [Functor.map_comp, Category.assoc]
  have hlast :=
    (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctorIsoMapDerivedCategory.inv.naturality
      ((rightDerivedLowerShriekBaseChangeMap A sq₁).app K)
  simp only [Functor.comp_obj] at hlast
  rw [← reassoc_of% hlast]


/-- Horizontal pasting of the specified compact-support exchange with equality-transported
outer maps. Source: thm-sf-kunneth-relative, base-change clause.
(blueprint: lem-sf-relative-kunneth-exchange-base-change).

Proof: substitute the two outer composite maps. Apply the general exchange-pasting
calculation, obtained from horizontal pasting in the exact inverse-image compact-support
formalism, and cancel the two pullback-composition isomorphisms. -/
theorem relativeKunneth_exchange_paste
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact f'']
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (a : X'' ⟶ X) (b : Y'' ⟶ Y) (ha : a = w' ≫ v') (hb : b = w ≫ v)
    (sq₃ : IsPullback a f'' f b) (K : DerivedCategoryModule A X) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v b hb).hom.app
        ((R(f)_![ModuleCat.{u + 1} A]).obj K) ≫
      (L((w)^*[ModuleCat.{u + 1} A])).map
        ((rightDerivedLowerShriekBaseChangeMap A sq₁).app K) ≫
      (rightDerivedLowerShriekBaseChangeMap A sq₂).app
        ((L((v')^*[ModuleCat.{u + 1} A])).obj K) ≫
      (R(f'')_![ModuleCat.{u + 1} A]).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v' a ha).inv.app K) =
      (rightDerivedLowerShriekBaseChangeMap A sq₃).app K := by
  subst a
  subst b
  have hp := relativeKunneth_exchange_paste_aux A sq₁ sq₂ K
  rw [reassoc_of% hp]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The exchange face of the relative-product base-change cube.
Source: thm-sf-kunneth-relative, base-change clause, the middle exchange factor.
(blueprint: lem-sf-relative-kunneth-exchange-base-change).

Proof: paste exchange first through the unprimed product square and then through its
base change on Y. Paste it a second way through the square for f and the primed product.
The two outer cartesian squares have the same arrows. Equality of their exchange maps,
followed by cancellation of the composition comparisons, gives the displayed face. -/
theorem relativeKunneth_exchange_cube
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B B' X X' Y Y' T T' : Scheme.{u}}
    {f : X ⟶ B} {f' : X' ⟶ B'} {g : Y ⟶ B} {g' : Y' ⟶ B'}
    {p : T ⟶ X} {q : T ⟶ Y} {p' : T' ⟶ X'} {q' : T' ⟶ Y'}
    {a : X' ⟶ X} {b : B' ⟶ B} {c : Y' ⟶ Y} {d : T' ⟶ T}
    [HasCompactification f] [HasCompactification f']
    [HasCompactification q] [HasCompactification q']
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact q] [QuasiCompact q']
    (sq : IsPullback p q f g) (sq' : IsPullback p' q' f' g')
    (sqf : IsPullback a f' f b) (sqg : IsPullback c g' g b)
    (sqq : IsPullback d q' q c) (sqp : CommSq d p' p a)
    (K : DerivedCategoryModule A X) :
    (L((c)^*[ModuleCat.{u + 1} A])).map
        ((rightDerivedLowerShriekBaseChangeMap A sq).app K) ≫
      (rightDerivedLowerShriekBaseChangeMap A sqq).app
        ((L((p)^*[ModuleCat.{u + 1} A])).obj K) ≫
      (R(q')_![ModuleCat.{u + 1} A]).map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqp).inv.app K) =
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqg.toCommSq).inv.app
        ((R(f)_![ModuleCat.{u + 1} A]).obj K) ≫
      (L((g')^*[ModuleCat.{u + 1} A])).map
        ((rightDerivedLowerShriekBaseChangeMap A sqf).app K) ≫
      (rightDerivedLowerShriekBaseChangeMap A sq').app
        ((L((a)^*[ModuleCat.{u + 1} A])).obj K) := by
  let outer := sqq.paste_horiz sq
  have h₁ := relativeKunneth_exchange_paste A sq sqq (d ≫ p) (c ≫ g) rfl rfl outer K
  have h₂ := relativeKunneth_exchange_paste A sqf sq' (d ≫ p) (c ≫ g)
    sqp.w sqg.w outer K
  apply (cancel_epi ((leftDerivedUpperStarComp
    (ModuleCat.{u + 1} A) c g).hom.app ((R(f)_![ModuleCat.{u + 1} A]).obj K))).1
  apply (cancel_mono ((R(q')_![ModuleCat.{u + 1} A]).map
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p' a (d ≫ p) sqp.w).inv.app K))).1
  simp only [derivedSquareUpperStarIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.comp_id]
  exact h₁.trans h₂.symm

private theorem relativeKunneth_exchange_cube_inv
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B B' X X' Y Y' T T' : Scheme.{u}}
    {f : X ⟶ B} {f' : X' ⟶ B'} {g : Y ⟶ B} {g' : Y' ⟶ B'}
    {p : T ⟶ X} {q : T ⟶ Y} {p' : T' ⟶ X'} {q' : T' ⟶ Y'}
    {a : X' ⟶ X} {b : B' ⟶ B} {c : Y' ⟶ Y} {d : T' ⟶ T}
    [HasCompactification f] [HasCompactification f']
    [HasCompactification q] [HasCompactification q']
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact q] [QuasiCompact q']
    (sq : IsPullback p q f g) (sq' : IsPullback p' q' f' g')
    (sqf : IsPullback a f' f b) (sqg : IsPullback c g' g b)
    (sqq : IsPullback d q' q c) (sqp : CommSq d p' p a)
    (K : DerivedCategoryModule A X) :
    (L((c)^*[ModuleCat.{u + 1} A])).map
        (rightDerivedLowerShriekBaseChangeIso A sq K).inv ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqg.toCommSq).inv.app
        ((R(f)_![ModuleCat.{u + 1} A]).obj K) ≫
      (L((g')^*[ModuleCat.{u + 1} A])).map
        ((rightDerivedLowerShriekBaseChangeMap A sqf).app K) =
    (rightDerivedLowerShriekBaseChangeMap A sqq).app
        ((L((p)^*[ModuleCat.{u + 1} A])).obj K) ≫
      (R(q')_![ModuleCat.{u + 1} A]).map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqp).inv.app K) ≫
      (rightDerivedLowerShriekBaseChangeIso A sq'
        ((L((a)^*[ModuleCat.{u + 1} A])).obj K)).inv := by
  apply (cancel_epi ((L((c)^*[ModuleCat.{u + 1} A])).map
    (rightDerivedLowerShriekBaseChangeIso A sq K).hom)).1
  apply (cancel_mono (rightDerivedLowerShriekBaseChangeIso A sq'
    ((L((a)^*[ModuleCat.{u + 1} A])).obj K)).hom).1
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  exact (relativeKunneth_exchange_cube A sq sq' sqf sqg sqq sqp K).symm

end AlgebraicGeometry.Etale
