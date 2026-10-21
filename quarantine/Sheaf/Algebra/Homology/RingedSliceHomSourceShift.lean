/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.Algebra.Homology.RingedSliceEvaluationModels
import all Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses

/-! # Slice restriction and normalized source shifts

Source: Stacks Project, Tags 08JB, 08FI and 0A8X.
(blueprint: lem-coef-slice-hom-source-shift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w w' a b x y
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedHomUniverses CategoryTheory.Pretriangulated.Opposite
namespace CategoryTheory

section Site
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]
  (U : C)
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w'} (Modules.{max c v, v, r} (J.over U) (R.over U))]

set_option quotPrecheck false
set_option hygiene false
local notation "H" => derivedInternalHomOfUniverses.{c, v, r, w} J R
local notation "HU" => derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)
local notation "F" =>
  letI := SheafOfModules.localizedSystemRestrictionAdditive.{c, v, r} R U
  letI := SheafOfModules.localizedSystemRestrictionLimits.{c, v, r} R U
  letI := SheafOfModules.localizedSystemRestrictionColimits.{c, v, r} R U
  Functor.mapDerivedCategory.{w, w'}
  (C₁ := Modules.{c, v, r} J R)
  (C₂ := Modules.{max c v, v, r} (J.over U) (R.over U))
  (SheafOfModules.localizedSystemRestriction.{c, v, r} R U)

/-- The augmentation normalization uniquely fixes the inverse comparison. -/
private theorem homModel_inv_eq
    (L I : Complex.{c, v, r} J R)
    (κ : (H).obj (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (complexHom.{c, v, r} J R L I))
    (hκ : RingedKInjectiveHomModel.{c, v, r, w} J R L I κ) :
    κ.inv = ringedSiteOrdinaryHomComparison.{c, v, r, w} J R L I := by
  have hn : κ.hom ≫ DerivedCategory.Q.map
      (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 L)
        ((ringedSiteHomAugmentation.{c, v, r} J R).app I)) =
      (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R L I).hom := by
    dsimp only [RingedKInjectiveHomModel] at hκ
    dsimp only [ringedSiteHomComplexMap, ringedSiteHomAugmentation,
      coefficientHomAugmentation]
    erw [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp]
    exact hκ
  apply (cancel_epi κ.hom).mp
  rw [Iso.hom_inv_id]
  dsimp only [ringedSiteOrdinaryHomComparison]
  rw [← Category.assoc, hn, Iso.hom_inv_id]

/-- Source reindexing on a normalized K-injective Hom model uses the same ordinary shift. -/
private theorem sourceShift_model
    (L I : Complex.{c, v, r} J R) (n : ℤ)
    (κ : (H).obj (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (complexHom.{c, v, r} J R L I))
    (κn : (H).obj (op (DerivedCategory.Q.obj (L⟦n⟧)), DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (complexHom.{c, v, r} J R (L⟦n⟧) I))
    (hκ : RingedKInjectiveHomModel.{c, v, r, w} J R L I κ)
    (hκn : RingedKInjectiveHomModel.{c, v, r, w} J R (L⟦n⟧) I κn) :
    ∃ e : (complexHom.{c, v, r} J R L I)⟦-n⟧ ≅
        complexHom.{c, v, r} J R (L⟦n⟧) I,
      LeftFormula.{c, v, r} J R L I n e ∧
      (DerivedCategory.Q.commShiftIso (-n)).hom.app (complexHom.{c, v, r} J R L I) ≫
          κ.inv⟦-n⟧' ≫
          (sourceShift.{c, v, r, w} J R (DerivedCategory.Q.obj L) n).hom.app
            (DerivedCategory.Q.obj I) =
        DerivedCategory.Q.map e.hom ≫ κn.inv ≫
          (H).map (Prod.mkHom ((DerivedCategory.Q.commShiftIso n).inv.app L).op
            (𝟙 (DerivedCategory.Q.obj I))) := by
  have hn := (leftShift_existsUnique.{c, v, r, w} J R).exists.choose_spec
    (DerivedCategory.Q.obj L) L I (Iso.refl _) n
  obtain ⟨e, he, hn⟩ := hn
  refine ⟨e, he, ?_⟩
  rw [homModel_inv_eq.{c, v, r, w} J R L I κ hκ,
    homModel_inv_eq.{c, v, r, w} J R (L⟦n⟧) I κn hκn]
  have hid : Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj L)))
      (𝟙 (DerivedCategory.Q.obj I)) =
      𝟙 (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) := rfl
  simpa only [sourceShift, Iso.refl_inv, op_id, hid, Functor.map_id,
    Category.comp_id, Category.id_comp, Functor.map_comp] using hn

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)] in
/-- Equality on every local Hom-family component is equality of chain maps. -/
private theorem homFamily_ext
    (L I K : Complex.{c, v, r} J R)
    (f g : K ⟶ complexHom.{c, v, r} J R L I)
    (h : ∀ (k p q : ℤ) (hpq : p + k = q) (V : C) (W : Over V)
      (z : (K.X k).val.obj (op V)) (x : (L.X p).val.obj (op W.left)),
      (((WeilConjectures.coefficientHomComponent.{r, c, v} J R L I k p q hpq).val.app
        (op V) ((f.f k).val.app (op V) z)).app (op W)).hom x =
      (((WeilConjectures.coefficientHomComponent.{r, c, v} J R L I k p q hpq).val.app
        (op V) ((g.f k).val.app (op V) z)).app (op W)).hom x) : f = g := by
  apply HomologicalComplex.hom_ext
  intro k
  apply homComplex_hom_ext
  intro p q hpq
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact h k p q hpq V.unop W.unop z x

private instance restrictionComplexCommShift :
    (ringedSliceComplexRestriction.{c, v, r} J R U).CommShift ℤ := by
  letI := (ringedOverFunctor_exactGeneral.{c, v, max c v r, max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r}
      RingCat.{max c v r})).obj R) U).1
  exact Functor.commShiftMapCochainComplex
    (SheafOfModules.overFunctor.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r}
        RingCat.{max c v r})).obj R) U)

omit [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]
  [HasDerivedCategory.{w'} (Modules.{max c v, v, r} (J.over U) (R.over U))] in
/-- Termwise slice restriction has the identity comparison in each shifted degree. -/
private theorem restrictionShift_component
    (L : Complex.{c, v, r} J R) (n k : ℤ) :
    (((ringedSliceComplexRestriction.{c, v, r} J R U).commShiftIso n).hom.app L).f k =
      𝟙 (((ringedSliceComplexRestriction.{c, v, r} J R U).obj L).X (k + n)) := by
  rfl

private def homRestrictionFormula
    (L I : Complex.{c, v, r} J R)
    (γ : (ringedSliceComplexRestriction.{c, v, r} J R U).obj
        (complexHom.{c, v, r} J R L I) ≅
      complexHom.{max c v, v, r} (J.over U) (R.over U)
        ((ringedSliceComplexRestriction.{c, v, r} J R U).obj L)
        ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I)) : Prop :=
  ∀ (k p q : ℤ) (h : p + k = q) (V : Over U) (W : Over V)
    (x : (L.X p).val.obj (op W.left.left))
    (z : ((complexHom.{c, v, r} J R L I).X k).val.obj (op V.left)),
    (((WeilConjectures.coefficientHomComponent.{r, max c v, v}
      (J.over U) (R.over U)
      ((ringedSliceComplexRestriction.{c, v, r} J R U).obj L)
      ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I) k p q h).val.app (op V)
      ((γ.hom.f k).val.app (op V) z)).app (op W)).hom x =
    (((WeilConjectures.coefficientHomComponent.{r, c, v} J R L I k p q h).val.app
      (op V.left) z).app (op (Over.mk W.hom.left))).hom x

section Chain
omit [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]
  [HasDerivedCategory.{w'} (Modules.{max c v, v, r} (J.over U) (R.over U))]

set_option maxHeartbeats 600000 in
-- Compare dependent Hom components on two sites with independent universes.
/-- On chain models restriction preserves the signed source reindexing. -/
private theorem restriction_sourceShift_chain
    (L I : Complex.{c, v, r} J R) (n : ℤ)
    (e : (complexHom.{c, v, r} J R L I)⟦-n⟧ ≅
      complexHom.{c, v, r} J R (L⟦n⟧) I)
    (eU : (complexHom.{max c v, v, r} (J.over U) (R.over U)
      ((ringedSliceComplexRestriction.{c, v, r} J R U).obj L)
      ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I))⟦-n⟧ ≅
      complexHom.{max c v, v, r} (J.over U) (R.over U)
        (((ringedSliceComplexRestriction.{c, v, r} J R U).obj L)⟦n⟧)
        ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I))
    (γ : (ringedSliceComplexRestriction.{c, v, r} J R U).obj
        (complexHom.{c, v, r} J R L I) ≅
      complexHom.{max c v, v, r} (J.over U) (R.over U)
        ((ringedSliceComplexRestriction.{c, v, r} J R U).obj L)
        ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I))
    (γn : (ringedSliceComplexRestriction.{c, v, r} J R U).obj
        (complexHom.{c, v, r} J R (L⟦n⟧) I) ≅
      complexHom.{max c v, v, r} (J.over U) (R.over U)
        ((ringedSliceComplexRestriction.{c, v, r} J R U).obj (L⟦n⟧))
        ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I))
    (he : LeftFormula.{c, v, r} J R L I n e)
    (heU : LeftFormula.{max c v, v, r} (J.over U) (R.over U)
      ((ringedSliceComplexRestriction.{c, v, r} J R U).obj L)
      ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I) n eU)
    (hγ : homRestrictionFormula.{c, v, r} J R U L I γ)
    (hγn : homRestrictionFormula.{c, v, r} J R U (L⟦n⟧) I γn) :
    (ringedSliceComplexRestriction.{c, v, r} J R U).map e.hom ≫ γn.hom =
      ((ringedSliceComplexRestriction.{c, v, r} J R U).commShiftIso (-n)).hom.app
          (complexHom.{c, v, r} J R L I) ≫
        γ.hom⟦-n⟧' ≫ eU.hom ≫
        ringedSiteHomComplexMap.{max c v, v, r} (J.over U) (R.over U)
          (((ringedSliceComplexRestriction.{c, v, r} J R U).commShiftIso n).hom.app L)
          (𝟙 ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I)) := by
  apply homFamily_ext.{max c v, v, r} (J.over U) (R.over U)
  intro k p q hpq V W z x
  have hm := homComplexFunctor_map_f_π
    (((ringedSliceComplexRestriction.{c, v, r} J R U).commShiftIso n).hom.app L)
    (𝟙 ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I)) k p q hpq
  simp only [restrictionShift_component, HomologicalComplex.id_f] at hm
  have hi : SheafOfModules.homObjMap
      (𝟙 (((ringedSliceComplexRestriction.{c, v, r} J R U).obj L).X (p + n)))
      (𝟙 (((ringedSliceComplexRestriction.{c, v, r} J R U).obj I).X q)) = 𝟙 _ :=
    by
      apply SheafOfModules.hom_ext
      ext V φ
      rfl
  have hm := hm.trans (congrArg (fun f ↦ _ ≫ f) hi)
  have hm := hm.trans (Category.comp_id _)
  have hl := hγn k p q hpq V W x ((e.hom.f k).val.app (op V.left) z)
  have he' := congrArg (fun f ↦ (((f.val.app (op V.left) z).app
    (op (Over.mk W.hom.left))).hom x)) (he k p q hpq)
  have hu := heU k p q hpq
  have hr :
      (((ringedSliceComplexRestriction.{c, v, r} J R U).commShiftIso (-n)).hom.app
            (complexHom.{c, v, r} J R L I) ≫
          γ.hom⟦-n⟧' ≫ eU.hom ≫
          ringedSiteHomComplexMap.{max c v, v, r} (J.over U) (R.over U)
            (((ringedSliceComplexRestriction.{c, v, r} J R U).commShiftIso n).hom.app L)
            (𝟙 ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I))).f k ≫
        homComplexπ (R := R.over U)
          ((ringedSliceComplexRestriction.{c, v, r} J R U).obj (L⟦n⟧))
          ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I) k p q hpq =
      γ.hom.f (k + -n) ≫ ((n * k).negOnePow •
        homComplexπ (R := R.over U)
          ((ringedSliceComplexRestriction.{c, v, r} J R U).obj L)
          ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I)
          (k + -n) (p + n) q (by omega)) := by
    have hr1 := congrArg (fun f ↦ γ.hom.f (k + -n) ≫ eU.hom.f k ≫ f) hm
    have hr2 := congrArg (fun f ↦ γ.hom.f (k + -n) ≫ f) hu
    exact hr1.trans hr2
  have hr' := congrArg (fun f ↦ (((f.val.app (op V) z).app (op W)).hom x)) hr
  have hg := hγ (k + -n) (p + n) q (by omega) V W x z
  rcases Int.even_or_odd (n * k) with hn | hn
  · have hs := Int.negOnePow_even (n * k) hn
    simp only [hs, one_smul] at he' hr'
    exact hl.trans (he'.trans (hg.symm.trans hr'.symm))
  · have hs := Int.negOnePow_odd (n * k) hn
    simp only [hs, Units.neg_smul, one_smul] at he' hr'
    change _ = -_ at he'
    change _ = -_ at hr'
    exact hl.trans (he'.trans ((congrArg Neg.neg hg.symm).trans hr'.symm))

end Chain

private instance derivedRestrictionCommShift :
    (ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U).CommShift ℤ :=
  inferInstanceAs ((F).CommShift ℤ)

private instance localizationCommShift : NatTrans.CommShift
    (ringedSliceLocalizationIso.{c, v, r, w, w'} J R U).hom ℤ := by
  let := SheafOfModules.localizedSystemRestrictionAdditive.{c, v, r} R U
  let := SheafOfModules.localizedSystemRestrictionLimits.{c, v, r} R U
  let := SheafOfModules.localizedSystemRestrictionColimits.{c, v, r} R U
  let : HasDerivedCategory.{w'} (SheafOfModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r}
        RingCat.{max c v r})).obj R).over U)) :=
    inferInstanceAs (HasDerivedCategory.{w'} (Modules.{max c v, v, r}
      (J.over U) (R.over U)))
  exact inferInstanceAs (NatTrans.CommShift
    (SheafOfModules.localizedSystemRestriction.{c, v, r} R U).mapDerivedCategoryFactors.hom ℤ)

/-- Shift compatibility of the fixed localization comparison, with both factors displayed. -/
private theorem localization_shift
    (L : Complex.{c, v, r} J R) (n : ℤ) :
    (F).map ((DerivedCategory.Q.commShiftIso n).hom.app L) ≫
        ((F).commShiftIso n).hom.app (DerivedCategory.Q.obj L) ≫
        ((ringedSliceLocalizationIso.{c, v, r, w, w'} J R U).hom.app L)⟦n⟧' =
      (ringedSliceLocalizationIso.{c, v, r, w, w'} J R U).hom.app (L⟦n⟧) ≫
        DerivedCategory.Q.map
          (((ringedSliceComplexRestriction.{c, v, r} J R U).commShiftIso n).hom.app L) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          ((ringedSliceComplexRestriction.{c, v, r} J R U).obj L) := by
  have h := NatTrans.shift_app_comm
    (ringedSliceLocalizationIso.{c, v, r, w, w'} J R U).hom n L
  simpa only [ringedSliceDerivedRestriction, ringedDerivedRestrictionGeneral,
    SheafOfModules.localizedSystemRestriction, Functor.commShiftIso_comp_hom_app,
    Category.assoc] using h

/-- Naturality of the fixed ordinary comparison in the source complex. -/
private theorem ordinaryComparison_source
    (L L' I : Complex.{c, v, r} J R) (f : L' ⟶ L) :
    DerivedCategory.Q.map (ringedSiteHomComplexMap.{c, v, r} J R f (𝟙 I)) ≫
        ringedSiteOrdinaryHomComparison.{c, v, r, w} J R L' I =
      ringedSiteOrdinaryHomComparison.{c, v, r, w} J R L I ≫
        (H).map (Prod.mkHom (DerivedCategory.Q.map f).op (𝟙 (DerivedCategory.Q.obj I))) := by
  have h := (ordinaryComparison.{c, v, r, w} J R).naturality
    (Prod.mkHom f.op (𝟙 I))
  simpa only [ordinaryComparison_app, Functor.comp_map, Functor.prod_map,
    Functor.op_map, Functor.map_id, ordinaryBifunctor, Functor.uncurry_obj_map,
    ringedSiteHomComplexMap, Quiver.Hom.unop_op, Functor.uncurry_obj_obj,
    homComplex] using h

/-- The normalized derived Hom comparison has a fixed formula on its chain models. -/
private theorem hom_restriction_model
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (MU : RingedSiteDualityModel.{max c v, v, r, w'} (J.over U) (R.over U))
    (d : RingedSliceEvaluationComparisons H HU
      (ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U) M.closed MU.closed
      (RingedSliceFlatRestriction.{c, v, r} J R U))
    (hh : RingedSliceHomModel.{c, v, r, w, w'} J R U
      M.closed M.models MU.closed MU.models d)
    (L I : Complex.{c, v, r} J R) [I.IsKInjective] :
    ∃ (κ : (H).obj (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≅
        DerivedCategory.Q.obj (complexHom.{c, v, r} J R L I))
      (κU : (HU).obj
        (op (DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, r} J R U).obj L)),
          DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I)) ≅
        DerivedCategory.Q.obj (complexHom.{max c v, v, r} (J.over U) (R.over U)
          ((ringedSliceComplexRestriction.{c, v, r} J R U).obj L)
          ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I)))
      (γ : (ringedSliceComplexRestriction.{c, v, r} J R U).obj
          (complexHom.{c, v, r} J R L I) ≅
        complexHom.{max c v, v, r} (J.over U) (R.over U)
          ((ringedSliceComplexRestriction.{c, v, r} J R U).obj L)
          ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I)),
      RingedKInjectiveHomModel.{c, v, r, w} J R L I κ ∧
      RingedKInjectiveHomModel.{max c v, v, r, w'} (J.over U) (R.over U)
        ((ringedSliceComplexRestriction.{c, v, r} J R U).obj L)
        ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I) κU ∧
      homRestrictionFormula.{c, v, r} J R U L I γ ∧
      (F).map κ.inv ≫ (d.eta (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I)).hom ≫
        (HU).map (Prod.mkHom
          ((ringedSliceLocalizationIso.{c, v, r, w, w'} J R U).inv.app L).op
          ((ringedSliceLocalizationIso.{c, v, r, w, w'} J R U).hom.app I)) =
        (ringedSliceLocalizationIso.{c, v, r, w, w'} J R U).hom.app
          (complexHom.{c, v, r} J R L I) ≫ DerivedCategory.Q.map γ.hom ≫ κU.inv := by
  obtain ⟨κ, κU, γ, hκ, hκU, hγ, he⟩ := hh L I
  refine ⟨κ, κU, γ, hκ, hκU, hγ, ?_⟩
  change (F).map κ.hom ≫ _ = _ at he
  have he' := congrArg (fun f ↦ (F).map κ.inv ≫ f ≫ κU.inv) he
  have hf := (Functor.mapIso (F) κ).inv_hom_id_assoc
    ((ringedSliceLocalizationIso.{c, v, r, w, w'} J R U).hom.app
      (complexHom.{c, v, r} J R L I) ≫ DerivedCategory.Q.map γ.hom ≫ κU.inv)
  simp only [Functor.mapIso_inv, Functor.mapIso_hom] at hf
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id, hf] using he'.symm

section ModelLeft
attribute [local irreducible] derivedInternalHomOfUniverses

set_option maxHeartbeats 600000 in
-- The source normalization and restriction square have dependent derived endpoints.
/-- The left side of the source-shift restriction square on normalized models. -/
private theorem sourceShift_model_restriction_left
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (MU : RingedSiteDualityModel.{max c v, v, r, w'} (J.over U) (R.over U))
    (d : RingedSliceEvaluationComparisons H HU
      (ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U) M.closed MU.closed
      (RingedSliceFlatRestriction.{c, v, r} J R U))
    (L I : Complex.{c, v, r} J R) (n : ℤ)
    (κ : (H).obj (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (complexHom.{c, v, r} J R L I))
    (κn : (H).obj (op (DerivedCategory.Q.obj (L⟦n⟧)), DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (complexHom.{c, v, r} J R (L⟦n⟧) I))
    (κUn : (HU).obj
      (op (DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, r} J R U).obj (L⟦n⟧))),
        DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I)) ≅
      DerivedCategory.Q.obj (complexHom.{max c v, v, r} (J.over U) (R.over U)
        ((ringedSliceComplexRestriction.{c, v, r} J R U).obj (L⟦n⟧))
        ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I)))
    (γn : (ringedSliceComplexRestriction.{c, v, r} J R U).obj
        (complexHom.{c, v, r} J R (L⟦n⟧) I) ≅
      complexHom.{max c v, v, r} (J.over U) (R.over U)
        ((ringedSliceComplexRestriction.{c, v, r} J R U).obj (L⟦n⟧))
        ((ringedSliceComplexRestriction.{c, v, r} J R U).obj I))
    (hκ : RingedKInjectiveHomModel.{c, v, r, w} J R L I κ)
    (hκn : RingedKInjectiveHomModel.{c, v, r, w} J R (L⟦n⟧) I κn) :
    let a := ringedSliceLocalizationIso.{c, v, r, w, w'} J R U
    (F).map κn.inv ≫ (d.eta (DerivedCategory.Q.obj (L⟦n⟧)) (DerivedCategory.Q.obj I)).hom ≫
        (HU).map (Prod.mkHom (a.app (L⟦n⟧)).inv.op (a.app I).hom) =
        (a.app (complexHom.{c, v, r} J R (L⟦n⟧) I)).hom ≫
          DerivedCategory.Q.map γn.hom ≫ κUn.inv →
    ∃ e : (complexHom.{c, v, r} J R L I)⟦-n⟧ ≅
        complexHom.{c, v, r} J R (L⟦n⟧) I,
      LeftFormula.{c, v, r} J R L I n e ∧
      (F).map ((DerivedCategory.Q.commShiftIso (-n)).hom.app
          (complexHom.{c, v, r} J R L I) ≫ κ.inv⟦-n⟧') ≫
        (F).map ((sourceShift.{c, v, r, w} J R (DerivedCategory.Q.obj L) n).hom.app
          (DerivedCategory.Q.obj I)) ≫
        (d.eta ((DerivedCategory.Q.obj L)⟦n⟧) (DerivedCategory.Q.obj I)).hom ≫
        (HU).map (Prod.mkHom
          ((a.app (L⟦n⟧)).inv ≫ (F).map ((DerivedCategory.Q.commShiftIso n).hom.app L)).op
          (a.app I).hom) =
        (F).map (DerivedCategory.Q.map e.hom) ≫
          (a.app (complexHom.{c, v, r} J R (L⟦n⟧) I)).hom ≫
          DerivedCategory.Q.map γn.hom ≫ κUn.inv := by
  intro a hmn
  obtain ⟨e, he, hs⟩ := sourceShift_model.{c, v, r, w} J R L I n κ κn hκ hκn
  refine ⟨e, he, ?_⟩
  let q := (HU).map (Prod.mkHom
    ((a.app (L⟦n⟧)).inv ≫ (F).map ((DerivedCategory.Q.commShiftIso n).hom.app L)).op
    (a.app I).hom)
  have heta := d.eta_naturality (DerivedCategory.Q.obj (L⟦n⟧))
    (DerivedCategory.Q.obj I) ((DerivedCategory.Q.obj L)⟦n⟧) (DerivedCategory.Q.obj I)
    ((DerivedCategory.Q.commShiftIso n).inv.app L) (𝟙 _)
  have ht :
      (F).map ((H).map (Prod.mkHom
          ((DerivedCategory.Q.commShiftIso n).inv.app L).op (𝟙 (DerivedCategory.Q.obj I)))) ≫
          (d.eta ((DerivedCategory.Q.obj L)⟦n⟧) (DerivedCategory.Q.obj I)).hom ≫ q =
      (d.eta (DerivedCategory.Q.obj (L⟦n⟧)) (DerivedCategory.Q.obj I)).hom ≫
        (HU).map (Prod.mkHom (a.app (L⟦n⟧)).inv.op (a.app I).hom) := by
    dsimp only [q]
    simp only [ringedSliceDerivedRestriction, ringedDerivedRestrictionGeneral,
      Functor.map_id] at heta
    rw [← Category.assoc, heta]
    simp only [Category.assoc, ← Functor.map_comp]
    congr 2
    ext <;> simp only [a, Prod.mkHom, SheafOfModules.localizedSystemRestriction,
      Functor.comp_obj, Iso.app_inv, Iso.app_hom, prod_comp, Category.id_comp,
      ← op_comp]
    apply congrArg Quiver.Hom.op
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [Functor.map_id, Category.comp_id]
  have hss := congrArg (fun f ↦ (F).map f ≫
    (d.eta ((DerivedCategory.Q.obj L)⟦n⟧) (DerivedCategory.Q.obj I)).hom ≫ q) hs
  simp only [Functor.map_comp, Category.assoc] at hss
  have ht' := congrArg (fun f ↦ (F).map (DerivedCategory.Q.map e.hom) ≫
    (F).map κn.inv ≫ f) ht
  have hm' := congrArg ((F).map (DerivedCategory.Q.map e.hom) ≫ ·) hmn
  simpa only [q, a, Iso.app_hom, RingedHomUniverses.Modules,
    Functor.map_comp, Category.assoc]
    using hss.trans (ht'.trans hm')

end ModelLeft

attribute [-instance] restrictionComplexCommShift derivedRestrictionCommShift localizationCommShift

/-- The normalized local Hom comparison preserves signed source reindexing.
Source: Stacks Project, sites-cohomology.tex, Tags 08JB and 0A8X.
(blueprint: lem-coef-slice-hom-source-shift).

Proof: choose a complex representative L of X and a K-injective I of Y.
The Hom-model hypothesis identifies the comparison with the restriction of local
families of maps, through the fixed augmentation comparisons. Choose the normalized
source shifts using leftShift_existsUnique on both sites. On the projection from
Hom degree k indexed by p, both composites reindex p to p+n and multiply by
(-1)^(n*k). Exact termwise restriction preserves this integer scalar, the source
and target differentials, and the reindexing. Equality on these projections gives
equality of chain maps. The Hom-model hypothesis supplies the normalized
comparison isomorphisms on both sites for these representatives. The localization
factorization is a morphism of shift functors.
For the conjugation, write a_L : F(Q L) ≅ Q_U(r L) for the localization
comparison, and κ, κ_U for the normalized Hom models. Their normalization gives
F(κ.inv) ≫ eta ≫ H_U(a_L.inv.op,a_I.hom) =
a_Hom ≫ Q_U(γ.hom) ≫ κ_U.inv; this is hom_restriction_model.
First take X = Q L and Y = Q I. Precompose the desired equation by
F(Q.cs(-n).hom ≫ κ.inv[-n]), and postcompose it by
H_U((a_(L[n]).inv ≫ F(Q.cs(n).hom)).op,a_I.hom).
Both are isomorphisms. The source LeftNormalization, naturality of eta,
and the normalized Hom-model square transform the left composite into
a_(Hom(L,I)[-n]) ≫ Q_U(r(e.hom) ≫ γ_n.hom) ≫ κ_Un.inv.
On the right, apply localization_shift at -n to the Hom complex and at n
to L. Move a_I through the target-naturality square of sourceShift_U.
Use LeftNormalization_U with representative isomorphism a_L.symm.
Naturality of the ordinary Hom comparison in the source moves the chain
map of r(L[n]) ≅ (r L)[n] through the last Hom model. The result is
a_(Hom(L,I)[-n]) ≫ Q_U(r.cs(-n).hom ≫ γ.hom[-n] ≫ e_U.hom ≫
Hom(r.cs(n).hom,id)) ≫ κ_Un.inv.
The proved restriction_sourceShift_chain identifies these two expressions.
Cancel the outside isomorphisms to get the derived equation on these models.
For a general source X, use a representative e_X : Q L ≅ X in both
LeftNormalizations, replacing a_L by F(e_X.symm) ≫ a_L in the same argument.
The two source maps introduced by e_X cancel by eta naturality. Finally,
represent Y by Q I ≅ Y with I K-injective and apply target naturality of
eta and both source-shift natural isomorphisms. This calculation works for
each integer n separately, including zero and negative n; it uses no
biduality or evaluation assertion. -/
theorem ringedSlice_hom_sourceShift
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (MU : RingedSiteDualityModel.{max c v, v, r, w'} (J.over U) (R.over U))
    (d : RingedSliceEvaluationComparisons H HU
      (ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U) M.closed MU.closed
      (RingedSliceFlatRestriction.{c, v, r} J R U))
    (hh : RingedSliceHomModel.{c, v, r, w, w'} J R U
      M.closed M.models MU.closed MU.models d) :
    ∀ (X Y : D.{c, v, r, w} J R) (n : ℤ),
      (F).map ((sourceShift.{c, v, r, w} J R X n).hom.app Y) ≫
          (d.eta (X⟦n⟧) Y).hom =
        ((F).commShiftIso (-n)).hom.app ((H).obj (op X, Y)) ≫
          ((d.eta X Y).hom)⟦-n⟧' ≫
          (sourceShift.{max c v, v, r, w'} (J.over U) (R.over U) ((F).obj X) n).hom.app
            ((F).obj Y) ≫
          (HU).map (Prod.mkHom (((F).commShiftIso n).hom.app X).op (𝟙 ((F).obj Y))) := by
  sorry

end Site
end CategoryTheory
