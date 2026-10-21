/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.Paper.RingedCoefficientProjectionData
import all Sheaf.CategoryTheory.GeometricModuleTransport
import all Sheaf.Paper.RingedCoefficientScalarUnits
import all Sheaf.Paper.RingedProjectionPullbackComparisons
import all Sheaf.Paper.KFlatRingedToposPullback
import all Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # The canonical inverse-image coefficient comparison

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0G7E and 07A6
(blueprint: lem-pur-coefficient-pullback-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits
open WeilConjectures.SemilinearSections (Mod D)
namespace SheafOfModules.RingedCoefficientProjection

attribute [local instance] SheafOfModules.sheafHasBinaryProduct

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}
  {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)
  {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := J) pY)
  (nX : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := K) pX)

private def addMap {R : Sheaf J CommRingCat.{r}} (M : Mod J R) :
    (underlying R).obj M ⨯ (underlying R).obj M ⟶ (underlying R).obj M :=
  ⟨{ app := fun U ↦ ↾fun t ↦
        (show M.val.obj U from (prod.fst : _ ⟶ (underlying R).obj M).hom.app U t) +
        (show M.val.obj U from (prod.snd : _ ⟶ (underlying R).obj M).hom.app U t)
     naturality := by
       intro U V f
       ext t
       have h₁ := CategoryTheory.congr_fun
         ((prod.fst : (underlying R).obj M ⨯ (underlying R).obj M ⟶
           (underlying R).obj M).hom.naturality f) t
       have h₂ := CategoryTheory.congr_fun
         ((prod.snd : (underlying R).obj M ⨯ (underlying R).obj M ⟶
           (underlying R).obj M).hom.naturality f) t
       change _ = M.val.map f (_ + _)
       rw [map_add]
       exact congrArg₂ (· + ·) h₁ h₂ }⟩

private def smulMap {R : Sheaf J CommRingCat.{r}} (M : Mod J R) :
    (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj R ⨯
      (underlying R).obj M ⟶ (underlying R).obj M :=
  ⟨{ app := fun U ↦ ↾fun t ↦
        (show R.obj.obj U from (prod.fst : _ ⟶
          (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj R).hom.app U t) •
        (show M.val.obj U from (prod.snd : _ ⟶ (underlying R).obj M).hom.app U t)
     naturality := by
       intro U V f
       ext t
       have h₁ := CategoryTheory.congr_fun
         ((prod.fst : (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj R ⨯
           (underlying R).obj M ⟶
           (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj R).hom.naturality f) t
       have h₂ := CategoryTheory.congr_fun
         ((prod.snd : (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj R ⨯
           (underlying R).obj M ⟶ (underlying R).obj M).hom.naturality f) t
       change _ = M.val.map f (_ • _)
       rw [M.val.map_smul]
       exact congrArg₂ (· • ·) h₁ h₂ }⟩

private def imagePair [PreservesFiniteLimits uInv]
    (A B : Sheaf J (Type r)) (U : Xᵒᵖ)
    (x : (uInv.obj A).obj.obj U) (y : (uInv.obj B).obj.obj U) :
    (uInv.obj (A ⨯ B)).obj.obj U :=
  (inv (prodComparison uInv A B)).hom.app U
    (SheafOfModules.sectionPair (uInv.obj A) (uInv.obj B) U x y)

omit [EssentiallySmall.{r} C] in
private theorem imagePair_fst [PreservesFiniteLimits uInv]
    (A B : Sheaf J (Type r)) (U : Xᵒᵖ)
    (x : (uInv.obj A).obj.obj U) (y : (uInv.obj B).obj.obj U) :
    (uInv.map (prod.fst : A ⨯ B ⟶ A)).hom.app U (imagePair A B U x y) = x := by
  change (inv (prodComparison uInv A B) ≫ uInv.map prod.fst).hom.app U _ = x
  rw [← prodComparison_fst, IsIso.inv_hom_id_assoc]
  exact SheafOfModules.sectionPair_fst _ _ _ _ _

omit [EssentiallySmall.{r} C] in
private theorem imagePair_snd [PreservesFiniteLimits uInv]
    (A B : Sheaf J (Type r)) (U : Xᵒᵖ)
    (x : (uInv.obj A).obj.obj U) (y : (uInv.obj B).obj.obj U) :
    (uInv.map (prod.snd : A ⨯ B ⟶ B)).hom.app U (imagePair A B U x y) = y := by
  change (inv (prodComparison uInv A B) ≫ uInv.map prod.snd).hom.app U _ = y
  rw [← prodComparison_snd, IsIso.inv_hom_id_assoc]
  exact SheafOfModules.sectionPair_snd _ _ _ _ _

private theorem underlying_restriction_map
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) {M N : Mod J S} (f : M ⟶ N) :
    (underlying R).map ((SuccessiveDerivedQuotient.restriction a).map f) =
      (underlying S).map f := rfl

private def restrictionUnderlying {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (M : Mod J S) :
    (underlying (g.rings.obj R)).obj
        ((g.inverse R).modules.obj ((SuccessiveDerivedQuotient.restriction a).obj M)) ≅
      (underlying (g.rings.obj R)).obj
        ((SuccessiveDerivedQuotient.restriction (g.rings.map a)).obj
          ((g.inverse S).modules.obj M)) :=
  (g.inverse R).moduleUnderlying.app
    ((SuccessiveDerivedQuotient.restriction a).obj M) ≪≫
      ((g.inverse S).moduleUnderlying.app M).symm

private theorem restrictionUnderlying_add [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Mod J S) (U : Xᵒᵖ)
    (x y : ((g.inverse R).modules.obj
      ((SuccessiveDerivedQuotient.restriction a).obj M)).val.obj U) :
    (restrictionUnderlying g a M).hom.hom.app U (x + y) =
      (show ((g.inverse S).modules.obj M).val.obj U from
        (restrictionUnderlying g a M).hom.hom.app U x) +
      (show ((g.inverse S).modules.obj M).val.obj U from
        (restrictionUnderlying g a M).hom.hom.app U y) := by
  let N := (SuccessiveDerivedQuotient.restriction a).obj M
  let A := (underlying S).obj M
  let e := (g.inverse R).moduleUnderlying.app N
  let p := imagePair A A U (e.hom.hom.app U x) (e.hom.hom.app U y)
  have hR := (g.inverse R).moduleAdd N (A ⨯ A) prod.fst prod.snd (addMap M)
    (fun _ _ ↦ rfl) U p
  have hS := (g.inverse S).moduleAdd M (A ⨯ A) prod.fst prod.snd (addMap M)
    (fun _ _ ↦ rfl) U p
  have hx : (e.inv).hom.app U ((uInv.map (prod.fst : A ⨯ A ⟶ A)).hom.app U p) = x := by
    rw [imagePair_fst]
    exact congrArg (fun k ↦ k.hom.app U x) e.hom_inv_id
  have hy : (e.inv).hom.app U ((uInv.map (prod.snd : A ⨯ A ⟶ A)).hom.app U p) = y := by
    rw [imagePair_snd]
    exact congrArg (fun k ↦ k.hom.app U y) e.hom_inv_id
  dsimp only [id] at hR hS
  change e.inv.hom.app U ((uInv.map (addMap M)).hom.app U p) =
    (show ((g.inverse R).modules.obj N).val.obj U from
      e.inv.hom.app U ((uInv.map (prod.fst : A ⨯ A ⟶ A)).hom.app U p)) +
    (show ((g.inverse R).modules.obj N).val.obj U from
      e.inv.hom.app U ((uInv.map (prod.snd : A ⨯ A ⟶ A)).hom.app U p)) at hR
  have hR' := hR.trans (congrArg₂ (· + ·) hx hy)
  let f : ((g.inverse R).modules.obj N).val.obj U →
      ((g.inverse S).modules.obj M).val.obj U := fun z ↦
    ((g.inverse S).moduleUnderlying.inv.app M).hom.app U (e.hom.hom.app U z)
  have h := congrArg f hR'
  have hc : f (e.inv.hom.app U ((uInv.map (addMap M)).hom.app U p)) =
      ((g.inverse S).moduleUnderlying.inv.app M).hom.app U
        ((uInv.map (addMap M)).hom.app U p) :=
    congrArg (fun z ↦ ((g.inverse S).moduleUnderlying.inv.app M).hom.app U z)
      (congrArg (fun k ↦ k.hom.app U ((uInv.map (addMap M)).hom.app U p)) e.inv_hom_id)
  change ((g.inverse S).moduleUnderlying.inv.app M).hom.app U
      ((uInv.map (addMap M)).hom.app U p) =
    (show ((g.inverse S).modules.obj M).val.obj U from
      ((g.inverse S).moduleUnderlying.inv.app M).hom.app U
        ((uInv.map (prod.fst : A ⨯ A ⟶ A)).hom.app U p)) +
    (show ((g.inverse S).modules.obj M).val.obj U from
      ((g.inverse S).moduleUnderlying.inv.app M).hom.app U
        ((uInv.map (prod.snd : A ⨯ A ⟶ A)).hom.app U p)) at hS
  have hS' := hS.trans (congrArg₂ (· + ·)
    (congrArg (fun z ↦ ((g.inverse S).moduleUnderlying.inv.app M).hom.app U z)
      (imagePair_fst A A U _ _))
    (congrArg (fun z ↦ ((g.inverse S).moduleUnderlying.inv.app M).hom.app U z)
      (imagePair_snd A A U _ _)))
  change f (x + y) = f x + f y
  exact h.symm.trans (hc.trans hS')

private theorem restrictionUnderlying_smul [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Mod J S) (U : Xᵒᵖ)
    (t : (g.rings.obj R).obj.obj U)
    (x : ((g.inverse R).modules.obj
      ((SuccessiveDerivedQuotient.restriction a).obj M)).val.obj U) :
    (restrictionUnderlying g a M).hom.hom.app U (t • x) =
      t • (show ((SuccessiveDerivedQuotient.restriction (g.rings.map a)).obj
        ((g.inverse S).modules.obj M)).val.obj U from
          (restrictionUnderlying g a M).hom.hom.app U x) := by
  let N := (SuccessiveDerivedQuotient.restriction a).obj M
  let A := (underlying S).obj M
  let B := (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj R
  let e := (g.inverse R).moduleUnderlying.app N
  let er := (g.inverse R).ringUnderlying
  let p := imagePair B A U (er.inv.hom.app U t) (e.hom.hom.app U x)
  let b : B ⨯ A ⟶ (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj S :=
    prod.fst ≫ (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).map a
  have hR := (g.inverse R).moduleSMul N (B ⨯ A) prod.fst prod.snd (smulMap N)
    (fun _ _ ↦ rfl) U p
  have hS := (g.inverse S).moduleSMul M (B ⨯ A) b prod.snd (smulMap N)
    (fun _ _ ↦ rfl) U p
  have ht : er.hom.hom.app U ((uInv.map (prod.fst : B ⨯ A ⟶ B)).hom.app U p) = t := by
    rw [imagePair_fst]
    exact congrArg (fun k ↦ k.hom.app U t) er.inv_hom_id
  have hx : e.inv.hom.app U ((uInv.map (prod.snd : B ⨯ A ⟶ A)).hom.app U p) = x := by
    rw [imagePair_snd]
    exact congrArg (fun k ↦ k.hom.app U x) e.hom_inv_id
  dsimp only [id] at hR hS
  change e.inv.hom.app U ((uInv.map (smulMap N)).hom.app U p) =
    (show (g.rings.obj R).obj.obj U from
      er.hom.hom.app U ((uInv.map (prod.fst : B ⨯ A ⟶ B)).hom.app U p)) •
      (show ((g.inverse R).modules.obj N).val.obj U from
        e.inv.hom.app U ((uInv.map (prod.snd : B ⨯ A ⟶ A)).hom.app U p)) at hR
  have hR' := hR.trans (congrArg₂ (· • ·) ht hx)
  change ((g.inverse S).moduleUnderlying.inv.app M).hom.app U
      ((uInv.map (smulMap N)).hom.app U p) =
    (show (g.rings.obj S).obj.obj U from
      (g.inverse S).ringUnderlying.hom.hom.app U ((uInv.map b).hom.app U p)) •
      (show ((g.inverse S).modules.obj M).val.obj U from
        ((g.inverse S).moduleUnderlying.inv.app M).hom.app U
          ((uInv.map (prod.snd : B ⨯ A ⟶ A)).hom.app U p)) at hS
  have hb : ((g.inverse S).ringUnderlying.hom).hom.app U
      ((uInv.map b).hom.app U p) = (g.rings.map a).hom.app U t := by
    have h := congrArg (fun k ↦ k.hom.app U
      ((uInv.map (prod.fst : B ⨯ A ⟶ B)).hom.app U p))
      (g.rings_naturality a)
    change ((g.inverse S).ringUnderlying.hom).hom.app U
        ((uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{r})).map a)).hom.app U
          ((uInv.map (prod.fst : B ⨯ A ⟶ B)).hom.app U p)) =
      (g.rings.map a).hom.app U
        (er.hom.hom.app U ((uInv.map (prod.fst : B ⨯ A ⟶ B)).hom.app U p)) at h
    rw [ht] at h
    simpa only [b, Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, types_comp_apply] using h
  have hp : (uInv.map (prod.snd : B ⨯ A ⟶ A)).hom.app U p =
      e.hom.hom.app U x := imagePair_snd B A U _ _
  have hS' := hS.trans (congrArg₂ (· • ·) hb
    (congrArg (fun z ↦ ((g.inverse S).moduleUnderlying.inv.app M).hom.app U z) hp))
  let f : ((g.inverse R).modules.obj N).val.obj U →
      ((g.inverse S).modules.obj M).val.obj U := fun z ↦
    ((g.inverse S).moduleUnderlying.inv.app M).hom.app U (e.hom.hom.app U z)
  have h := congrArg f hR'
  have hc : f (e.inv.hom.app U ((uInv.map (smulMap N)).hom.app U p)) =
      ((g.inverse S).moduleUnderlying.inv.app M).hom.app U
        ((uInv.map (smulMap N)).hom.app U p) :=
    congrArg (fun z ↦ ((g.inverse S).moduleUnderlying.inv.app M).hom.app U z)
      (congrArg (fun k ↦ k.hom.app U ((uInv.map (smulMap N)).hom.app U p)) e.inv_hom_id)
  change f (t • x) = (g.rings.map a).hom.app U t • f x
  exact h.symm.trans (hc.trans hS')

private def restrictionMap [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Mod J S) :
    (g.inverse R).modules.obj ((SuccessiveDerivedQuotient.restriction a).obj M) ⟶
      (SuccessiveDerivedQuotient.restriction (g.rings.map a)).obj
        ((g.inverse S).modules.obj M) :=
  SheafOfModules.linearLift (restrictionUnderlying g a M).hom
    (restrictionUnderlying_add g a M) (restrictionUnderlying_smul g a M)

private theorem restrictionMap_isIso [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Mod J S) :
    IsIso (restrictionMap g a M) := by
  have : IsIso ((underlying (g.rings.obj R)).map (restrictionMap g a M)) := by
    change IsIso (restrictionUnderlying g a M).hom
    infer_instance
  exact isIso_of_reflects_iso (restrictionMap g a M) (underlying (g.rings.obj R))

private def restrictionIso [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    SuccessiveDerivedQuotient.restriction a ⋙ (g.inverse R).modules ≅
      (g.inverse S).modules ⋙ SuccessiveDerivedQuotient.restriction (g.rings.map a) := by
  have := restrictionMap_isIso g a
  refine NatIso.ofComponents (fun M ↦ asIso (restrictionMap g a M)) ?_
  intro M N f
  apply (underlying (g.rings.obj R)).map_injective
  change (underlying (g.rings.obj R)).map
      ((g.inverse R).modules.map ((SuccessiveDerivedQuotient.restriction a).map f)) ≫
        (restrictionUnderlying g a N).hom =
      (restrictionUnderlying g a M).hom ≫
        (underlying (g.rings.obj S)).map ((g.inverse S).modules.map f)
  have hR := (g.inverse R).moduleUnderlying.hom.naturality
    ((SuccessiveDerivedQuotient.restriction a).map f)
  have hS := (g.inverse S).moduleUnderlying.inv.naturality f
  dsimp only [Functor.comp_map] at hR hS
  dsimp only [restrictionUnderlying, Iso.trans_hom, Iso.symm_hom]
  erw [← Category.assoc, hR, Category.assoc, hS]
  rfl

private theorem restrictionIso_hom_underlying [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Mod J S) :
    (underlying (g.rings.obj R)).map ((restrictionIso g a).hom.app M) =
      (g.inverse R).moduleUnderlying.hom.app
          ((SuccessiveDerivedQuotient.restriction a).obj M) ≫
        (g.inverse S).moduleUnderlying.inv.app M := rfl

attribute [local irreducible] restrictionMap restrictionIso

private theorem adjunction_underlying
    (R : Sheaf J CommRingCat.{r}) (M : Mod J R) (N : Mod K (g.rings.obj R))
    (f : (g.inverse R).modules.obj M ⟶ N) :
    (underlying R).map ((g.ordinaryAdjunction R).homEquiv M N f) ≫
        (g.pushUnderlying R).hom.app N =
      adj.homEquiv _ _ ((g.inverse R).moduleUnderlying.inv.app M ≫
        (underlying (g.rings.obj R)).map f) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  have hn := (g.pushUnderlying R).hom.naturality f
  change (underlying R).map ((g.push R).map f) ≫
      (g.pushUnderlying R).hom.app N =
    (g.pushUnderlying R).hom.app ((g.inverse R).modules.obj M) ≫
      uPush.map ((underlying (g.rings.obj R)).map f) at hn
  rw [Category.assoc, hn]
  change _ = adj.unit.app ((underlying R).obj M) ≫
    uPush.map ((g.inverse R).moduleUnderlying.inv.app M ≫
      (underlying (g.rings.obj R)).map f)
  rw [← g.unit_underlying R M, Functor.map_comp]
  simp only [Category.assoc, ← uPush.map_comp, Iso.hom_inv_id_app_assoc]

private def pushRestriction [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    g.push S ⋙ SuccessiveDerivedQuotient.restriction a ⟶
      SuccessiveDerivedQuotient.restriction (g.rings.map a) ⋙ g.push R :=
  (mateEquiv (g.ordinaryAdjunction S) (g.ordinaryAdjunction R)
    (TwoSquare.mk _ _ _ _ (restrictionIso g a).hom)).natTrans

private theorem pushRestriction_underlying [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (N : Mod K (g.rings.obj S)) :
    (underlying R).map ((pushRestriction g a).app N) ≫
        (g.pushUnderlying R).hom.app
          ((SuccessiveDerivedQuotient.restriction (g.rings.map a)).obj N) =
      (g.pushUnderlying S).hom.app N := by
  let f := (restrictionIso g a).hom.app ((g.push S).obj N) ≫
    (SuccessiveDerivedQuotient.restriction (g.rings.map a)).map
      ((g.ordinaryAdjunction S).counit.app N)
  have hm : (g.ordinaryAdjunction R).homEquiv _ _ f =
      (pushRestriction g a).app N := by
    apply ((g.ordinaryAdjunction R).homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact (mateEquiv_counit (g.ordinaryAdjunction S) (g.ordinaryAdjunction R)
      (TwoSquare.mk _ _ _ _ (restrictionIso g a).hom) N).symm
  rw [← hm]
  erw [adjunction_underlying g]
  have hf : (g.inverse R).moduleUnderlying.inv.app
        ((SuccessiveDerivedQuotient.restriction a).obj ((g.push S).obj N)) ≫
        (underlying (g.rings.obj R)).map f =
      (g.inverse S).moduleUnderlying.inv.app ((g.push S).obj N) ≫
        (underlying (g.rings.obj S)).map ((g.ordinaryAdjunction S).counit.app N) := by
    dsimp only [f]
    rw [Functor.map_comp, underlying_restriction_map, restrictionIso_hom_underlying]
    erw [Category.assoc, Iso.inv_hom_id_app_assoc]
  refine (congrArg (adj.homEquiv _ _) hf).trans ?_
  refine (adjunction_underlying g S ((g.push S).obj N) N
    ((g.ordinaryAdjunction S).counit.app N)).symm.trans ?_
  have hc : (g.ordinaryAdjunction S).homEquiv ((g.push S).obj N) N
      ((g.ordinaryAdjunction S).counit.app N) = 𝟙 _ := by
    apply ((g.ordinaryAdjunction S).homEquiv _ N).symm.injective
    rw [Equiv.symm_apply_apply]
    exact (Adjunction.homEquiv_symm_id (g.ordinaryAdjunction S) N).symm
  rw [hc, CategoryTheory.Functor.map_id, Category.id_comp]

private def pushRestrictionIso [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    g.push S ⋙ SuccessiveDerivedQuotient.restriction a ≅
      SuccessiveDerivedQuotient.restriction (g.rings.map a) ⋙ g.push R := by
  have h (N : Mod K (g.rings.obj S)) : IsIso ((pushRestriction g a).app N) := by
    have he : (underlying R).map ((pushRestriction g a).app N) =
        (g.pushUnderlying S).hom.app N ≫
          (g.pushUnderlying R).inv.app
            ((SuccessiveDerivedQuotient.restriction (g.rings.map a)).obj N) := by
      apply (cancel_mono ((g.pushUnderlying R).hom.app _)).1
      rw [pushRestriction_underlying, Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
    have : IsIso ((underlying R).map ((pushRestriction g a).app N)) := by
      rw [he]
      infer_instance
    exact isIso_of_reflects_iso _ (underlying R)
  letI : ∀ N, IsIso ((pushRestriction g a).app N) := h
  haveI := NatIso.isIso_of_isIso_app (pushRestriction g a)
  exact asIso (pushRestriction g a)

private def ordinaryBackward [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    (g.inverse R).modules ⋙ (pX (g.rings.map a)).ordinary ⟶
      (pY a).ordinary ⋙ (g.inverse S).modules :=
  ((mateEquiv (nY.ordinaryAdjunction a) (nX.ordinaryAdjunction (g.rings.map a))).symm
    (TwoSquare.mk _ _ _ _ (restrictionIso g a).hom)).natTrans

private theorem ordinaryBackward_isIso [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    IsIso (ordinaryBackward g nY nX a) := by
  have he : conjugateEquiv
      ((nY.ordinaryAdjunction a).comp (g.ordinaryAdjunction S))
      ((g.ordinaryAdjunction R).comp (nX.ordinaryAdjunction (g.rings.map a)))
      (ordinaryBackward g nY nX a) = pushRestriction g a := by
    let β := (mateEquiv (nY.ordinaryAdjunction a)
      (nX.ordinaryAdjunction (g.rings.map a))).symm
        (TwoSquare.mk _ _ _ _ (restrictionIso g a).hom)
    have h := iterated_mateEquiv_conjugateEquiv
      (nY.ordinaryAdjunction a) (nX.ordinaryAdjunction (g.rings.map a))
      (g.ordinaryAdjunction R) (g.ordinaryAdjunction S) β
    simpa only [β, ordinaryBackward, pushRestriction, Equiv.apply_symm_apply] using h.symm
  have : IsIso (pushRestriction g a) := by
    change IsIso (pushRestrictionIso g a).hom
    infer_instance
  have : IsIso (conjugateEquiv
      ((nY.ordinaryAdjunction a).comp (g.ordinaryAdjunction S))
      ((g.ordinaryAdjunction R).comp (nX.ordinaryAdjunction (g.rings.map a)))
      (ordinaryBackward g nY nX a)) := by rw [he]; infer_instance
  exact conjugateEquiv_of_iso
    ((nY.ordinaryAdjunction a).comp (g.ordinaryAdjunction S))
    ((g.ordinaryAdjunction R).comp (nX.ordinaryAdjunction (g.rings.map a)))
    (ordinaryBackward g nY nX a)

private def ordinaryComparison [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    (pY a).ordinary ⋙ (g.inverse S).modules ≅
      (g.inverse R).modules ⋙ (pX (g.rings.map a)).ordinary := by
  have := ordinaryBackward_isIso g nY nX a
  exact (asIso (ordinaryBackward g nY nX a)).symm

private theorem ordinaryComparison_insertion [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Mod J R) :
    uInv.map (insertion nY a M) ≫
        (g.inverse S).moduleUnderlying.inv.app ((pY a).ordinary.obj M) ≫
        (underlying (g.rings.obj S)).map ((ordinaryComparison g nY nX a).hom.app M) =
      (g.inverse R).moduleUnderlying.inv.app M ≫
        insertion nX (g.rings.map a) ((g.inverse R).modules.obj M) := by
  have hu := unit_mateEquiv_symm (nY.ordinaryAdjunction a)
    (nX.ordinaryAdjunction (g.rings.map a))
    (TwoSquare.mk _ _ _ _ (restrictionIso g a).hom) M
  change (g.inverse R).modules.map ((nY.ordinaryAdjunction a).unit.app M) ≫
      (restrictionIso g a).hom.app ((pY a).ordinary.obj M) =
    (nX.ordinaryAdjunction (g.rings.map a)).unit.app ((g.inverse R).modules.obj M) ≫
      (SuccessiveDerivedQuotient.restriction (g.rings.map a)).map
        ((ordinaryBackward g nY nX a).app M) at hu
  have h := congrArg (fun f ↦ (g.inverse R).moduleUnderlying.inv.app M ≫
    (underlying (g.rings.obj R)).map f) hu
  simp only [Functor.map_comp, underlying_restriction_map,
    restrictionIso_hom_underlying] at h
  change (g.inverse R).moduleUnderlying.inv.app M ≫
      (underlying (g.rings.obj R)).map
        ((g.inverse R).modules.map ((nY.ordinaryAdjunction a).unit.app M)) ≫
      (g.inverse R).moduleUnderlying.hom.app
        ((SuccessiveDerivedQuotient.restriction a).obj ((pY a).ordinary.obj M)) ≫
      (g.inverse S).moduleUnderlying.inv.app ((pY a).ordinary.obj M) =
    (g.inverse R).moduleUnderlying.inv.app M ≫
      insertion nX (g.rings.map a) ((g.inverse R).modules.obj M) ≫
      (underlying (g.rings.obj S)).map ((ordinaryComparison g nY nX a).inv.app M) at h
  have hn := (g.inverse R).moduleUnderlying.inv.naturality
    ((nY.ordinaryAdjunction a).unit.app M)
  change uInv.map (insertion nY a M) ≫
      (g.inverse R).moduleUnderlying.inv.app
        ((SuccessiveDerivedQuotient.restriction a).obj ((pY a).ordinary.obj M)) =
    (g.inverse R).moduleUnderlying.inv.app M ≫
      (underlying (g.rings.obj R)).map
        ((g.inverse R).modules.map ((nY.ordinaryAdjunction a).unit.app M)) at hn
  erw [← Category.assoc, ← hn, Category.assoc,
    Iso.inv_hom_id_app_assoc] at h
  rw [← Category.assoc, h]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

include nX in
private theorem inverse_preserves_flat [PreservesFiniteLimits uInv]
    (R : Sheaf J CommRingCat.{r}) (P : CochainComplex (Mod J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients
        (((g.inverse R).modules.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ i : ℤ, IsFlatOnSite (J := K) (R := g.rings.obj R)
        ((((g.inverse R).modules.mapHomologicalComplex (.up ℤ)).obj P).X i) := by
  let I := (g.inverse R).modules
  let q := pX (𝟙 (g.rings.obj R))
  let F := I ⋙ q.ordinary
  have he : ∀ M, F.obj M = changeOfRings (𝟙 (g.rings.obj R)) (I.obj M) :=
    fun M ↦ q.obj_eq (I.obj M)
  have hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (he M) ≫
      changeOfRingsHom (𝟙 (g.rings.obj R)) (I.obj M) (I.map f) ≫ eqToHom (he N).symm :=
    fun f ↦ q.map_eq (I.map f)
  obtain ⟨hF, ht⟩ := isKFlat_ringedToposPullback uInv uPush adj (g.inverse R)
    (𝟙 (g.rings.obj R)) F he hm P hP hf
  let e : F ≅ I := Functor.isoWhiskerLeft I (ordinaryUnit nX (g.rings.obj R)) ≪≫
    Functor.rightUnitor I
  let ep := (NatIso.mapHomologicalComplex e (.up ℤ)).app P
  refine ⟨SheafOfModules.kFlat_iso_independent (g.rings.obj R) ep hF, ?_⟩
  intro i
  exact SheafOfModules.flatOnSite_of_iso (g.rings.obj R) (e.app (P.X i)) (ht i)

private def computationNat {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    DerivedCategory.Q ⋙ (pY a).derived ⟶
      (pY a).ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso (Mod J R)).inv (pY a).derived ≫
    Functor.whiskerLeft (HomotopyCategory.quotient (Mod J R) (.up ℤ)) (pY a).counit ≫
    Functor.whiskerRight ((pY a).ordinary.mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerLeft ((pY a).ordinary.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso (Mod J S)).hom

private theorem computationNat_app {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Mod J R) ℤ) :
    (computationNat (pY := pY) a).app P = computation (pY a) P := rfl

include nY in
private theorem computation_isIso {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Mod J R) ℤ) (hP : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) :
    IsIso ((computationNat (pY := pY) a).app P) := by
  have := nY.computed a P hP hf
  dsimp only [computationNat, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

private def flatComplex (R : Sheaf J CommRingCat.{r}) :
    ObjectProperty (CochainComplex (Mod J R) ℤ) :=
  fun P ↦ P.IsKFlatIndependentCoefficients ∧
    ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)

private def flatHomotopy (R : Sheaf J CommRingCat.{r}) :
    ObjectProperty (HomotopyCategory (Mod J R) (.up ℤ)) :=
  fun P ↦ flatComplex R P.as

private def flatQuotient (R : Sheaf J CommRingCat.{r}) :
    (flatComplex R).FullSubcategory ⥤ (flatHomotopy R).FullSubcategory where
  obj P := ⟨(HomotopyCategory.quotient _ _).obj P.obj, P.property⟩
  map f := ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map f.hom)

private theorem flatQuotient_full (R : Sheaf J CommRingCat.{r}) :
    (flatQuotient R).Full :=
  { map_surjective := fun f ↦ ⟨ObjectProperty.homMk f.hom.out, by
      apply ObjectProperty.hom_ext
      exact HomotopyCategory.quotient_map_out f.hom⟩ }

private theorem flatQuotient_essSurj (R : Sheaf J CommRingCat.{r}) :
    (flatQuotient R).EssSurj :=
  { mem_essImage := fun P ↦ ⟨⟨P.obj.as, P.property⟩, ⟨Iso.refl _⟩⟩ }

private theorem flat_localization (R : Sheaf J CommRingCat.{r}) :
    ((flatHomotopy R).ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso (Mod J R) (.up ℤ)).inverseImage (flatHomotopy R).ι) := by
  apply SheafOfModules.restriction_localization
    (HomotopyCategory.quasiIso (Mod J R) (.up ℤ)) DerivedCategory.Qh (flatHomotopy R)
  intro H
  obtain ⟨P, f, hk, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients H.as
  have hs : ∀ i, IsFlatOnSite (J := J) (R := R) (P.X i) := fun i ↦
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X i)).symm (hf i)
  refine ⟨⟨(HomotopyCategory.quotient (Mod J R) (.up ℤ)).obj P, hk, hs⟩,
    (HomotopyCategory.quotient (Mod J R) (.up ℤ)).map f, ?_⟩
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq

private theorem flat_iso_descent (R : Sheaf J CommRingCat.{r})
    {E : Type*} [Category E] (U V : D J R ⥤ E)
    (e : ((flatComplex R).ι ⋙ DerivedCategory.Q) ⋙ U ≅
      ((flatComplex R).ι ⋙ DerivedCategory.Q) ⋙ V) :
    ∃ t : U ≅ V,
      Functor.isoWhiskerLeft ((flatComplex R).ι ⋙ DerivedCategory.Q) t = e := by
  let P := flatHomotopy R
  let F := flatQuotient R
  let : F.Full := flatQuotient_full R
  let : F.EssSurj := flatQuotient_essSurj R
  let L := P.ι ⋙ DerivedCategory.Qh
  let K := (flatComplex R).ι ⋙ DerivedCategory.Q
  let eK : F ⋙ L ≅ K := NatIso.ofComponents
    (fun X ↦ (DerivedCategory.quotientCompQhIso (Mod J R)).app X.obj)
    (fun f ↦ (DerivedCategory.quotientCompQhIso (Mod J R)).hom.naturality f.hom)
  let W := (HomotopyCategory.quasiIso (Mod J R) (.up ℤ)).inverseImage P.ι
  have : L.IsLocalization W := flat_localization R
  exact SheafOfModules.ProjectionCoherence.localization_iso_descent F L W K eK U V e

private def leftComputation {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    DerivedCategory.Q ⋙ ((pY a).derived ⋙ g.left S) ⟶
      ((pY a).ordinary.mapHomologicalComplex (.up ℤ) ⋙
        (g.inverse S).modules.mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (computationNat (pY := pY) a) (g.left S) ≫
    Functor.whiskerLeft ((pY a).ordinary.mapHomologicalComplex (.up ℤ))
      (g.inverse S).modules.mapDerivedCategoryFactors.hom

private def rightComputation {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    DerivedCategory.Q ⋙ (g.left R ⋙ (pX (g.rings.map a)).derived) ⟶
      ((g.inverse R).modules.mapHomologicalComplex (.up ℤ) ⋙
        (pX (g.rings.map a)).ordinary.mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (g.inverse R).modules.mapDerivedCategoryFactors.hom
      (pX (g.rings.map a)).derived ≫
    Functor.whiskerLeft ((g.inverse R).modules.mapHomologicalComplex (.up ℤ))
      (computationNat (pY := pX) (g.rings.map a))

private theorem leftComputation_app {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Mod J R) ℤ) :
    (leftComputation (pY := pY) g a).app P =
      (g.left S).map (computation (pY a) P) ≫
        (g.inverse S).modules.mapDerivedCategoryFactors.hom.app
          (((pY a).ordinary.mapHomologicalComplex (.up ℤ)).obj P) := by
  change (g.left S).map ((computationNat (pY := pY) a).app P) ≫ _ = _
  exact congrArg (fun f ↦ (g.left S).map f ≫
    (g.inverse S).modules.mapDerivedCategoryFactors.hom.app
      (((pY a).ordinary.mapHomologicalComplex (.up ℤ)).obj P)) (computationNat_app a P)

private theorem rightComputation_app {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Mod J R) ℤ) :
    (rightComputation (pX := pX) g a).app P =
      (pX (g.rings.map a)).derived.map
          ((g.inverse R).modules.mapDerivedCategoryFactors.hom.app P) ≫
        computation (pX (g.rings.map a))
          (((g.inverse R).modules.mapHomologicalComplex (.up ℤ)).obj P) := by
  change (pX (g.rings.map a)).derived.map
      ((g.inverse R).modules.mapDerivedCategoryFactors.hom.app P) ≫
      (computationNat (pY := pX) (g.rings.map a)).app
        (((g.inverse R).modules.mapHomologicalComplex (.up ℤ)).obj P) = _
  exact congrArg (fun f ↦ (pX (g.rings.map a)).derived.map
    ((g.inverse R).modules.mapDerivedCategoryFactors.hom.app P) ≫ f)
      (computationNat_app (g.rings.map a)
        (((g.inverse R).modules.mapHomologicalComplex (.up ℤ)).obj P))

private def leftFlatComputation {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    (flatComplex R).ι ⋙ DerivedCategory.Q ⋙ ((pY a).derived ⋙ g.left S) ≅
      (flatComplex R).ι ⋙ ((pY a).ordinary.mapHomologicalComplex (.up ℤ) ⋙
        (g.inverse S).modules.mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q := by
  have hi (P : (flatComplex R).FullSubcategory) :
      IsIso ((Functor.whiskerLeft (flatComplex R).ι (leftComputation (pY := pY) g a)).app P) := by
    have := computation_isIso nY a P.obj P.property.1 P.property.2
    dsimp only [leftComputation, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, ObjectProperty.ι_obj]
    infer_instance
  letI : ∀ P, IsIso
      ((Functor.whiskerLeft (flatComplex R).ι (leftComputation (pY := pY) g a)).app P) := hi
  haveI := NatIso.isIso_of_isIso_app
    (Functor.whiskerLeft (flatComplex R).ι (leftComputation (pY := pY) g a))
  exact asIso (Functor.whiskerLeft (flatComplex R).ι (leftComputation (pY := pY) g a))

private def rightFlatComputation [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    (flatComplex R).ι ⋙ DerivedCategory.Q ⋙ (g.left R ⋙ (pX (g.rings.map a)).derived) ≅
      (flatComplex R).ι ⋙ ((g.inverse R).modules.mapHomologicalComplex (.up ℤ) ⋙
        (pX (g.rings.map a)).ordinary.mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q := by
  have hi (P : (flatComplex R).FullSubcategory) :
      IsIso ((Functor.whiskerLeft (flatComplex R).ι (rightComputation (pX := pX) g a)).app P) := by
    obtain ⟨hk, hf⟩ := inverse_preserves_flat g nX R P.obj P.property.1 P.property.2
    have := computation_isIso nX (g.rings.map a)
      (((g.inverse R).modules.mapHomologicalComplex (.up ℤ)).obj P.obj) hk hf
    dsimp only [rightComputation, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, ObjectProperty.ι_obj]
    infer_instance
  letI : ∀ P, IsIso
      ((Functor.whiskerLeft (flatComplex R).ι (rightComputation (pX := pX) g a)).app P) := hi
  haveI := NatIso.isIso_of_isIso_app
    (Functor.whiskerLeft (flatComplex R).ι (rightComputation (pX := pX) g a))
  exact asIso (Functor.whiskerLeft (flatComplex R).ι (rightComputation (pX := pX) g a))

private theorem leftFlatComputation_hom_app
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : (flatComplex R).FullSubcategory) :
    (leftFlatComputation g nY a).hom.app P =
      (leftComputation (pY := pY) g a).app P.obj := rfl

private theorem rightFlatComputation_hom_app [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : (flatComplex R).FullSubcategory) :
    (rightFlatComputation g nX a).hom.app P =
      (rightComputation (pX := pX) g a).app P.obj := rfl

attribute [local irreducible] leftFlatComputation rightFlatComputation

private theorem derivedComparison_exists [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    ∃ e : (pY a).derived ⋙ g.left S ≅ g.left R ⋙ (pX (g.rings.map a)).derived,
      ∀ (P : CochainComplex (Mod J R) ℤ), P.IsKFlatIndependentCoefficients →
        (∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) →
        e.hom.app (DerivedCategory.Q.obj P) ≫ (rightComputation (pX := pX) g a).app P =
          (leftComputation (pY := pY) g a).app P ≫ DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (ordinaryComparison g nY nX a).hom
              (.up ℤ)).app P) := by
  let c : (pY a).ordinary.mapHomologicalComplex (.up ℤ) ⋙
      (g.inverse S).modules.mapHomologicalComplex (.up ℤ) ≅
      (g.inverse R).modules.mapHomologicalComplex (.up ℤ) ⋙
        (pX (g.rings.map a)).ordinary.mapHomologicalComplex (.up ℤ) :=
    Functor.mapHomologicalComplexCompIso (ordinaryComparison g nY nX a) (.up ℤ)
  let m : (flatComplex R).ι ⋙ ((pY a).ordinary.mapHomologicalComplex (.up ℤ) ⋙
        (g.inverse S).modules.mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q ≅
      (flatComplex R).ι ⋙ ((g.inverse R).modules.mapHomologicalComplex (.up ℤ) ⋙
        (pX (g.rings.map a)).ordinary.mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft (flatComplex R).ι (Functor.isoWhiskerRight c DerivedCategory.Q)
  let l := leftFlatComputation g nY a
  let r := rightFlatComputation g nX a
  obtain ⟨e, he⟩ := flat_iso_descent R
    ((pY a).derived ⋙ g.left S) (g.left R ⋙ (pX (g.rings.map a)).derived)
    (l ≪≫ m ≪≫ r.symm)
  refine ⟨e, ?_⟩
  intro P hk hf
  let T : (flatComplex R).FullSubcategory := ⟨P, hk, hf⟩
  have h := NatTrans.congr_app (congrArg Iso.hom he) T
  change e.hom.app (DerivedCategory.Q.obj P) =
    l.hom.app T ≫ m.hom.app T ≫ r.inv.app T at h
  have h' : e.hom.app (DerivedCategory.Q.obj P) ≫ r.hom.app T =
      l.hom.app T ≫ m.hom.app T := by
    rw [h, Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hl : l.hom.app T = (leftComputation (pY := pY) g a).app P :=
    leftFlatComputation_hom_app g nY a T
  have hr : r.hom.app T = (rightComputation (pX := pX) g a).app P :=
    rightFlatComputation_hom_app g nX a T
  have hc : c.hom.app P =
      (NatTrans.mapHomologicalComplex (ordinaryComparison g nY nX a).hom (.up ℤ)).app P := by
    ext i
    rfl
  have hm : m.hom.app T = DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (ordinaryComparison g nY nX a).hom
        (.up ℤ)).app P) := by
    change DerivedCategory.Q.map (c.hom.app P) = _
    exact congrArg DerivedCategory.Q.map hc
  exact (congrArg (e.hom.app (DerivedCategory.Q.obj P) ≫ ·) hr.symm).trans
    (h'.trans (congrArg₂ (· ≫ ·) hl hm))

/-- The canonical coefficient/inverse-image tensor square has normalized ordinary
and derived comparison isomorphisms.

Source: Stacks Project, Cohomology on Sites, Tag 0D6D
(lemma-derived-pullback-composition) and Tag 0G7E (lemma-pullback-K-flat);
Modules on Sites, Tags 03D2 and 03EL
(blueprint: lem-pur-coefficient-pullback-comparison).

Proof:
1. Finite-product comparisons and the algebraic inverse-image graph equations
identify inverse image followed by restriction with restriction followed by
inverse image. Its geometric mate is invertible: under the underlying-sheaf
adjunction it is the specified direct-image identification. Iterating mates
therefore gives an invertible scalar-extension comparison. The unit formula
for mates proves ordinary_insertion.
2. Choose a flat-term K-flat resolution. Coefficient inverse image preserves
K-flat complexes and flat terms by 0G7E. Ordinary scalar extension preserves the
appropriate acyclic K-flat comparisons. Therefore both composites are computed
on this same resolution. Localize the ordinary isomorphism, cancelling the
invertible K-flat computation counits, to obtain the derived isomorphism.
3. The localization equation is exactly Comparisons.representative: apply the
ordinary comparison to the resolved complex, and transport the two computation
counits through the canonical mapDerivedCategoryFactors isomorphisms. Naturality
in the complex and independence of resolution follow from localization
uniqueness. This is the comparison of the two factorizations in 0D6D, in the
changed coefficient category. No coefficient map is assumed flat. -/
theorem coefficientPullbackComparisons [PreservesFiniteLimits uInv] :
    Nonempty (Comparisons g nY nX) := by
  classical
  refine ⟨{
    ordinary := ordinaryComparison g nY nX
    ordinary_insertion := ordinaryComparison_insertion g nY nX
    derived := fun {R S} a ↦ Classical.choose (derivedComparison_exists g nY nX a)
    representative := ?_ }⟩
  intro R S a P hk hf
  have h := Classical.choose_spec (derivedComparison_exists g nY nX a) P hk hf
  rw [leftComputation_app, rightComputation_app] at h
  simpa only [Category.assoc] using h

end SheafOfModules.RingedCoefficientProjection

end
