/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import Sheaf.CategoryTheory.Sites.LocalizedSetPullbackComparison

/-! # The canonical commutative-ring comparison for localization of a site

Source: Stacks Project, Sites, Tag 03CF; Modules on Sites, Tag 04J0.
(blueprint: lem-weil-pbc-slice-commRing-pullback-isIso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
namespace CategoryTheory

/-- Transport the section formulas along equality of internal rings.
Source: Stacks Tag 00YR, rings as sextuples. Eliminate the equality of rings;
proof irrelevance identifies the two carrier equalities, so the formulas agree. -/
private theorem transportRingSectionOperations.{v, w} {C : Type v} [Category C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget CommRingCat.{w})]
    (A : Sheaf J CommRingCat.{w}) (Y X : CommRingObjCat (Sheaf J (Type w)))
    (p : Y = X) (h : Y.X = (sheafForget J).obj A)
    (k : (sheafForget J).obj A = X.X) (Z : Cᵒᵖ)
    (ops :
      (∀ a b, (eqToHom h).hom.app Z
        ((AddMonObj.add (X := Y.X)).hom.app Z (a, b)) =
          (show A.obj.obj Z from (eqToHom h).hom.app Z a) +
            (show A.obj.obj Z from (eqToHom h).hom.app Z b)) ∧
      (∀ t, (eqToHom h).hom.app Z ((AddMonObj.zero (X := Y.X)).hom.app Z t) =
        (0 : A.obj.obj Z)) ∧
      (∀ a b, (eqToHom h).hom.app Z ((MonObj.mul (X := Y.X)).hom.app Z (a, b)) =
          (show A.obj.obj Z from (eqToHom h).hom.app Z a) *
            (show A.obj.obj Z from (eqToHom h).hom.app Z b)) ∧
      (∀ t, (eqToHom h).hom.app Z ((MonObj.one (X := Y.X)).hom.app Z t) =
        (1 : A.obj.obj Z))) :
      (∀ a b, (eqToHom k.symm).hom.app Z
        ((AddMonObj.add (X := X.X)).hom.app Z (a, b)) =
          (show A.obj.obj Z from (eqToHom k.symm).hom.app Z a) +
            (show A.obj.obj Z from (eqToHom k.symm).hom.app Z b)) ∧
      (∀ t, (eqToHom k.symm).hom.app Z ((AddMonObj.zero (X := X.X)).hom.app Z t) =
        (0 : A.obj.obj Z)) ∧
      (∀ a b, (eqToHom k.symm).hom.app Z ((MonObj.mul (X := X.X)).hom.app Z (a, b)) =
          (show A.obj.obj Z from (eqToHom k.symm).hom.app Z a) *
            (show A.obj.obj Z from (eqToHom k.symm).hom.app Z b)) ∧
      (∀ t, (eqToHom k.symm).hom.app Z ((MonObj.one (X := X.X)).hom.app Z t) =
        (1 : A.obj.obj Z)) := by
  cases p
  exact ops

private theorem ringDirectImageOperations
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : C ⥤ D) [f.IsContinuous J K]
    (FU : Sheaf K CommRingCat.{u} ⥤
      CommRingObjCat (Sheaf K (Type u)))
    (GU : CommRingObjCat (Sheaf K (Type u)) ⥤
      Sheaf K CommRingCat.{u})
    (hFU : FU ⋙ CommRingObjCat.forget _ = sheafForget K)
    (hGU : GU ⋙ sheafForget K = CommRingObjCat.forget _)
    (hGUFU : GU ⋙ FU = 𝟭 _)
    (opsU : (∀ (A : Sheaf K CommRingCat.{u}) (Z : Dᵒᵖ),
        (∀ a b : (FU.obj A).X.obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z
            ((AddMonObj.add (X := (FU.obj A).X)).hom.app Z (a, b)) =
            (show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z a) +
              (show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z b)) ∧
        (∀ t : (𝟙_ (Sheaf K (Type u))).obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z ((AddMonObj.zero (X := (FU.obj A).X)).hom.app Z t) =
            (0 : A.obj.obj Z)) ∧
        (∀ a : (FU.obj A).X.obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z ((AddGrpObj.neg (X := (FU.obj A).X)).hom.app Z a) =
            -(show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z a)) ∧
        (∀ a b : (FU.obj A).X.obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z ((MonObj.mul (X := (FU.obj A).X)).hom.app Z (a, b)) =
            (show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z a) *
              (show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z b)) ∧
        (∀ t : (𝟙_ (Sheaf K (Type u))).obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z ((MonObj.one (X := (FU.obj A).X)).hom.app Z t) =
            (1 : A.obj.obj Z))))
    (FV : Sheaf J CommRingCat.{u} ⥤
      CommRingObjCat (Sheaf J (Type u)))
    (GV : CommRingObjCat (Sheaf J (Type u)) ⥤
      Sheaf J CommRingCat.{u})
    (hFV : FV ⋙ CommRingObjCat.forget _ = sheafForget J)
    (hGV : GV ⋙ sheafForget J = CommRingObjCat.forget _)
    (hGVFV : GV ⋙ FV = 𝟭 _)
    (opsV : (∀ (A : Sheaf J CommRingCat.{u}) (Z : Cᵒᵖ),
        (∀ a b : (FV.obj A).X.obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z
            ((AddMonObj.add (X := (FV.obj A).X)).hom.app Z (a, b)) =
            (show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z a) +
              (show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type u))).obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z ((AddMonObj.zero (X := (FV.obj A).X)).hom.app Z t) =
            (0 : A.obj.obj Z)) ∧
        (∀ a : (FV.obj A).X.obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z ((AddGrpObj.neg (X := (FV.obj A).X)).hom.app Z a) =
            -(show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z a)) ∧
        (∀ a b : (FV.obj A).X.obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z ((MonObj.mul (X := (FV.obj A).X)).hom.app Z (a, b)) =
            (show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z a) *
              (show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type u))).obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z ((MonObj.one (X := (FV.obj A).X)).hom.app Z t) =
            (1 : A.obj.obj Z)))) :
    let b := f
    let R := b.sheafPushforwardContinuous (Type u)
      J K
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u}
      J K
    ∀ (RF : CommRingObjCat (Sheaf K (Type u)) ⥤
          CommRingObjCat (Sheaf J (Type u)))
      (hRF : RF ⋙ CommRingObjCat.forget _ = CommRingObjCat.forget _ ⋙ R)
      [PreservesFiniteProducts R],
      (∀ X : CommRingObjCat (Sheaf K (Type u)),
            AddMonObj.add (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              ((eqToIso hRF).hom.app X ⊗ₘ (eqToIso hRF).hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (AddMonObj.add (X := X.X)) ∧
            AddMonObj.zero (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (AddMonObj.zero (X := X.X)) ∧
            AddGrpObj.neg (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              (eqToIso hRF).hom.app X ≫ R.map (AddGrpObj.neg (X := X.X)) ∧
            MonObj.mul (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              ((eqToIso hRF).hom.app X ⊗ₘ (eqToIso hRF).hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (MonObj.one (X := X.X))) →
      ∀ X (Z : Cᵒᵖ),
        let c : (GV.obj (RF.obj X)).obj.obj Z → (Rr.obj (GU.obj X)).obj.obj Z :=
          ((eqToIso hGV).hom.app (RF.obj X) ≫
          (eqToIso hRF).hom.app X ≫ R.map ((eqToIso hGU).inv.app X)).hom.app Z
        (∀ a b : (GV.obj (RF.obj X)).obj.obj Z, c (a + b) = c a + c b) ∧
        c (0 : (GV.obj (RF.obj X)).obj.obj Z) = 0 ∧
        (∀ a b : (GV.obj (RF.obj X)).obj.obj Z, c (a * b) = c a * c b) ∧
        c (1 : (GV.obj (RF.obj X)).obj.obj Z) = 1 := by
  dsimp only
  intro RF hRF _ hOps X Z
  have hu (W : Dᵒᵖ) := transportRingSectionOperations (GU.obj X)
    (FU.obj (GU.obj X)) X (Functor.congr_obj hGUFU X)
    (Functor.congr_obj hFU (GU.obj X)) (Functor.congr_obj hGU X) W
    (by
      have hh := opsU (GU.obj X) W
      simp only [eqToIso.hom, eqToHom_app] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.2.1, hh.2.2.2.2⟩)
  have hv := transportRingSectionOperations (GV.obj (RF.obj X))
    (FV.obj (GV.obj (RF.obj X))) (RF.obj X) (Functor.congr_obj hGVFV (RF.obj X))
    (Functor.congr_obj hFV (GV.obj (RF.obj X))) (Functor.congr_obj hGV (RF.obj X)) Z
    (by
      have hh := opsV (GV.obj (RF.obj X)) Z
      simp only [eqToIso.hom, eqToHom_app] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.2.1, hh.2.2.2.2⟩)
  let b := f
  let R := b.sheafPushforwardContinuous (Type u)
    J K
  let eU := (eqToIso hGU).app X
  let eV := (eqToIso hGV).app (RF.obj X)
  let eR := (eqToIso hRF).app X
  have kU : eU.inv = eqToHom (Functor.congr_obj hGU X).symm := by
    change (eqToIso hGU).inv.app X = _
    rw [eqToIso.inv, eqToHom_app]
  have kV : eV.inv = eqToHom (Functor.congr_obj hGV (RF.obj X)).symm := by
    change (eqToIso hGV).inv.app (RF.obj X) = _
    rw [eqToIso.inv, eqToHom_app]
  have hu' := hu (b.op.obj Z)
  rw [← kU] at hu'
  rw [← kV] at hv
  have hprod (a d : (R.obj X.X).obj.obj Z) :
      (prodComparisonIso R X.X X.X).inv.hom.app Z (a, d) = (a, d) := by
    have hf : (prodComparisonIso R X.X X.X).inv ≫ R.map (fst X.X X.X) =
        fst (R.obj X.X) (R.obj X.X) := by
      apply (prodComparisonIso R X.X X.X).inv_comp_eq.mpr
      simp only [prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_fst]
    have hs : (prodComparisonIso R X.X X.X).inv ≫ R.map (snd X.X X.X) =
        snd (R.obj X.X) (R.obj X.X) := by
      apply (prodComparisonIso R X.X X.X).inv_comp_eq.mpr
      simp only [prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_snd]
    apply Prod.ext
    · exact congrArg (fun g => g.hom.app Z (a, d)) hf
    · exact congrArg (fun g => g.hom.app Z (a, d)) hs
  have hVI (a : (GV.obj (RF.obj X)).obj.obj Z) :
      eV.inv.hom.app Z (eV.hom.hom.app Z a) = a :=
    congrArg (fun g => g.hom.app Z a) eV.hom_inv_id
  have hVH (a : (RF.obj X).X.obj.obj Z) :
      eV.hom.hom.app Z (eV.inv.hom.app Z a) = a :=
    congrArg (fun g => g.hom.app Z a) eV.inv_hom_id
  have hinj {a d : (RF.obj X).X.obj.obj Z}
      (h : eV.inv.hom.app Z a = eV.inv.hom.app Z d) : a = d := by
    have hh := congrArg (fun x => eV.hom.hom.app Z x) h
    simpa only [hVH] using hh
  have hvadd (a d : (GV.obj (RF.obj X)).obj.obj Z) :
      eV.hom.hom.app Z (a + d) =
        (AddMonObj.add (X := (RF.obj X).X)).hom.app Z
          (eV.hom.hom.app Z a, eV.hom.hom.app Z d) := by
    apply hinj
    exact (hVI (a + d)).trans
      ((hv.1 (eV.hom.hom.app Z a) (eV.hom.hom.app Z d)).trans
        (congrArg₂ (fun x y : (GV.obj (RF.obj X)).obj.obj Z => x + y)
          (hVI a) (hVI d))).symm
  have hvmul (a d : (GV.obj (RF.obj X)).obj.obj Z) :
      eV.hom.hom.app Z (a * d) =
        (MonObj.mul (X := (RF.obj X).X)).hom.app Z
          (eV.hom.hom.app Z a, eV.hom.hom.app Z d) := by
    apply hinj
    exact (hVI (a * d)).trans
      ((hv.2.2.1 (eV.hom.hom.app Z a) (eV.hom.hom.app Z d)).trans
        (congrArg₂ (fun x y : (GV.obj (RF.obj X)).obj.obj Z => x * y)
          (hVI a) (hVI d))).symm
  have hvzero : eV.hom.hom.app Z (0 : (GV.obj (RF.obj X)).obj.obj Z) =
      (AddMonObj.zero (X := (RF.obj X).X)).hom.app Z PUnit.unit := by
    apply hinj
    exact (hVI 0).trans (hv.2.1 PUnit.unit).symm
  have hvone : eV.hom.hom.app Z (1 : (GV.obj (RF.obj X)).obj.obj Z) =
      (MonObj.one (X := (RF.obj X).X)).hom.app Z PUnit.unit := by
    apply hinj
    exact (hVI 1).trans (hv.2.2.2 PUnit.unit).symm
  have hradd (a d : (RF.obj X).X.obj.obj Z) :
      eR.hom.hom.app Z ((AddMonObj.add (X := (RF.obj X).X)).hom.app Z (a, d)) =
        (AddMonObj.add (X := X.X)).hom.app (b.op.obj Z)
          (eR.hom.hom.app Z a, eR.hom.hom.app Z d) := by
    have hh := congrArg (fun g => g.hom.app Z (a, d)) (hOps X).1
    change eR.hom.hom.app Z
      ((AddMonObj.add (X := (RF.obj X).X)).hom.app Z (a, d)) =
        (AddMonObj.add (X := X.X)).hom.app (b.op.obj Z)
          ((prodComparisonIso R X.X X.X).inv.hom.app Z
            (eR.hom.hom.app Z a, eR.hom.hom.app Z d)) at hh
    rw [hprod] at hh
    exact hh
  have hrmul (a d : (RF.obj X).X.obj.obj Z) :
      eR.hom.hom.app Z ((MonObj.mul (X := (RF.obj X).X)).hom.app Z (a, d)) =
        (MonObj.mul (X := X.X)).hom.app (b.op.obj Z)
          (eR.hom.hom.app Z a, eR.hom.hom.app Z d) := by
    have hh := congrArg (fun g => g.hom.app Z (a, d)) (hOps X).2.2.2.1
    change eR.hom.hom.app Z
      ((MonObj.mul (X := (RF.obj X).X)).hom.app Z (a, d)) =
        (MonObj.mul (X := X.X)).hom.app (b.op.obj Z)
          ((prodComparisonIso R X.X X.X).inv.hom.app Z
            (eR.hom.hom.app Z a, eR.hom.hom.app Z d)) at hh
    rw [hprod] at hh
    exact hh
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a d
    change eU.inv.hom.app (b.op.obj Z) (eR.hom.hom.app Z (eV.hom.hom.app Z (a + d))) =
      (show (GU.obj X).obj.obj (b.op.obj Z) from
        eU.inv.hom.app (b.op.obj Z) (eR.hom.hom.app Z (eV.hom.hom.app Z a))) +
        (show (GU.obj X).obj.obj (b.op.obj Z) from
          eU.inv.hom.app (b.op.obj Z) (eR.hom.hom.app Z (eV.hom.hom.app Z d)))
    rw [hvadd, hradd]
    exact hu'.1 _ _
  · change eU.inv.hom.app (b.op.obj Z)
      (eR.hom.hom.app Z (eV.hom.hom.app Z (0 : (GV.obj (RF.obj X)).obj.obj Z))) =
        (0 : (GU.obj X).obj.obj (b.op.obj Z))
    rw [hvzero]
    have hh := congrArg (fun g => g.hom.app Z PUnit.unit) (hOps X).2.1
    change eR.hom.hom.app Z
      ((AddMonObj.zero (X := (RF.obj X).X)).hom.app Z PUnit.unit) =
        (AddMonObj.zero (X := X.X)).hom.app (b.op.obj Z)
          ((preservesTerminalIso R).inv.hom.app Z PUnit.unit) at hh
    rw [hh]
    exact hu'.2.1 _
  · intro a d
    change eU.inv.hom.app (b.op.obj Z) (eR.hom.hom.app Z (eV.hom.hom.app Z (a * d))) =
      (show (GU.obj X).obj.obj (b.op.obj Z) from
        eU.inv.hom.app (b.op.obj Z) (eR.hom.hom.app Z (eV.hom.hom.app Z a))) *
        (show (GU.obj X).obj.obj (b.op.obj Z) from
          eU.inv.hom.app (b.op.obj Z) (eR.hom.hom.app Z (eV.hom.hom.app Z d)))
    rw [hvmul, hrmul]
    exact hu'.2.2.1 _ _
  · change eU.inv.hom.app (b.op.obj Z)
      (eR.hom.hom.app Z (eV.hom.hom.app Z (1 : (GV.obj (RF.obj X)).obj.obj Z))) =
        (1 : (GU.obj X).obj.obj (b.op.obj Z))
    rw [hvone]
    have hh := congrArg (fun g => g.hom.app Z PUnit.unit) (hOps X).2.2.2.2
    change eR.hom.hom.app Z
      ((MonObj.one (X := (RF.obj X).X)).hom.app Z PUnit.unit) =
        (MonObj.one (X := X.X)).hom.app (b.op.obj Z)
          ((preservesTerminalIso R).inv.hom.app Z PUnit.unit) at hh
    rw [hh]
    exact hu'.2.2.2 _


private theorem ringDirectImageComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : C ⥤ D) [f.IsContinuous J K]
    (FU : Sheaf K CommRingCat.{u} ⥤
      CommRingObjCat (Sheaf K (Type u)))
    (GU : CommRingObjCat (Sheaf K (Type u)) ⥤
      Sheaf K CommRingCat.{u})
    (hFU : FU ⋙ CommRingObjCat.forget _ = sheafForget K)
    (hGU : GU ⋙ sheafForget K = CommRingObjCat.forget _)
    (hGUFU : GU ⋙ FU = 𝟭 _)
    (opsU : (∀ (A : Sheaf K CommRingCat.{u}) (Z : Dᵒᵖ),
        (∀ a b : (FU.obj A).X.obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z
            ((AddMonObj.add (X := (FU.obj A).X)).hom.app Z (a, b)) =
            (show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z a) +
              (show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z b)) ∧
        (∀ t : (𝟙_ (Sheaf K (Type u))).obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z ((AddMonObj.zero (X := (FU.obj A).X)).hom.app Z t) =
            (0 : A.obj.obj Z)) ∧
        (∀ a : (FU.obj A).X.obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z ((AddGrpObj.neg (X := (FU.obj A).X)).hom.app Z a) =
            -(show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z a)) ∧
        (∀ a b : (FU.obj A).X.obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z ((MonObj.mul (X := (FU.obj A).X)).hom.app Z (a, b)) =
            (show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z a) *
              (show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z b)) ∧
        (∀ t : (𝟙_ (Sheaf K (Type u))).obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z ((MonObj.one (X := (FU.obj A).X)).hom.app Z t) =
            (1 : A.obj.obj Z))))
    (FV : Sheaf J CommRingCat.{u} ⥤
      CommRingObjCat (Sheaf J (Type u)))
    (GV : CommRingObjCat (Sheaf J (Type u)) ⥤
      Sheaf J CommRingCat.{u})
    (hFV : FV ⋙ CommRingObjCat.forget _ = sheafForget J)
    (hGV : GV ⋙ sheafForget J = CommRingObjCat.forget _)
    (hGVFV : GV ⋙ FV = 𝟭 _)
    (opsV : (∀ (A : Sheaf J CommRingCat.{u}) (Z : Cᵒᵖ),
        (∀ a b : (FV.obj A).X.obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z
            ((AddMonObj.add (X := (FV.obj A).X)).hom.app Z (a, b)) =
            (show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z a) +
              (show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type u))).obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z ((AddMonObj.zero (X := (FV.obj A).X)).hom.app Z t) =
            (0 : A.obj.obj Z)) ∧
        (∀ a : (FV.obj A).X.obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z ((AddGrpObj.neg (X := (FV.obj A).X)).hom.app Z a) =
            -(show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z a)) ∧
        (∀ a b : (FV.obj A).X.obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z ((MonObj.mul (X := (FV.obj A).X)).hom.app Z (a, b)) =
            (show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z a) *
              (show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type u))).obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z ((MonObj.one (X := (FV.obj A).X)).hom.app Z t) =
            (1 : A.obj.obj Z)))) :
    let b := f
    let R := b.sheafPushforwardContinuous (Type u)
      J K
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u}
      J K
    ∀ (RF : CommRingObjCat (Sheaf K (Type u)) ⥤
          CommRingObjCat (Sheaf J (Type u)))
      (hRF : RF ⋙ CommRingObjCat.forget _ = CommRingObjCat.forget _ ⋙ R)
      [PreservesFiniteProducts R],
      (∀ X : CommRingObjCat (Sheaf K (Type u)),
            AddMonObj.add (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              ((eqToIso hRF).hom.app X ⊗ₘ (eqToIso hRF).hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (AddMonObj.add (X := X.X)) ∧
            AddMonObj.zero (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (AddMonObj.zero (X := X.X)) ∧
            AddGrpObj.neg (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              (eqToIso hRF).hom.app X ≫ R.map (AddGrpObj.neg (X := X.X)) ∧
            MonObj.mul (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              ((eqToIso hRF).hom.app X ⊗ₘ (eqToIso hRF).hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (MonObj.one (X := X.X))) →
      ∃ d : RF ⋙ GV ≅ GU ⋙ Rr,
        ∀ X, (sheafForget J).map (d.hom.app X) =
          (eqToIso hGV).hom.app (RF.obj X) ≫ (eqToIso hRF).hom.app X ≫
            R.map ((eqToIso hGU).inv.app X) := by
  dsimp only
  intro RF hRF hprod opsR
  obtain h := ringDirectImageOperations J K f
    FU GU hFU hGU hGUFU opsU FV GV hFV hGV hGVFV opsV RF hRF opsR
  let α X : (sheafForget J).obj (GV.obj (RF.obj X)) ⟶
      (sheafForget J).obj
        ((f.sheafPushforwardContinuous
          CommRingCat.{u} J
          K).obj (GU.obj X)) :=
    (eqToIso hGV).hom.app (RF.obj X) ≫ (eqToIso hRF).hom.app X ≫
      (f.sheafPushforwardContinuous
        (Type u) J
        K).map ((eqToIso hGU).inv.app X)
  let dh X : GV.obj (RF.obj X) ⟶
      (f.sheafPushforwardContinuous
        CommRingCat.{u} J
        K).obj (GU.obj X) :=
    ⟨{ app Z := CommRingCat.ofHom
        { toFun := (α X).hom.app Z
          map_zero' := (h X Z).2.1
          map_add' := (h X Z).1
          map_one' := (h X Z).2.2.2
          map_mul' := (h X Z).2.2.1 }
       naturality := by
         intro Z W g
         ext a
         exact ConcreteCategory.congr_hom ((α X).hom.naturality g) a }⟩
  have hh X : (sheafForget J).map (dh X) = α X := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext Z
    ext a
    rfl
  have hi X : IsIso (dh X) := by
    have hm : IsIso ((sheafForget J).map (dh X)) := by
      rw [hh]
      dsimp only [α]
      infer_instance
    exact isIso_of_reflects_iso (dh X) (sheafForget J)
  let d := fun X ↦ @asIso _ _ _ _ (dh X) (hi X)
  have hd X : (sheafForget J).map (d X).hom =
      (eqToIso hGV).hom.app (RF.obj X) ≫ (eqToIso hRF).hom.app X ≫
        (f.sheafPushforwardContinuous
          (Type u) J
          K).map ((eqToIso hGU).inv.app X) := hh X
  refine ⟨NatIso.ofComponents d ?_, hd⟩
  intro X Y g
  apply (sheafForget J).map_injective
  simp only [Functor.map_comp, Functor.comp_map]
  rw [hd, hd]
  have hnV := (eqToIso hGV).hom.naturality (RF.map g)
  have hnR := (eqToIso hRF).hom.naturality g
  have hnU := (eqToIso hGU).inv.naturality g
  dsimp only [Functor.comp_map] at hnV hnR hnU
  simp only [Category.assoc]
  rw [← Category.assoc, hnV]
  simp only [Category.assoc]
  rw [← Category.assoc ((CommRingObjCat.forget _).map (RF.map g)), hnR]
  simp only [Category.assoc]
  rw [← Functor.map_comp]
  have ht := congrArg
    (f.sheafPushforwardContinuous
      (Type u) J
      K).map hnU
  exact congrArg (fun k ↦ (eqToIso hGV).hom.app (RF.obj X) ≫
    (eqToIso hRF).hom.app X ≫ k) ht |>.trans (by
      simp only [Functor.map_comp]
      rfl)


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Source: Stacks Project, Proposition 00YV, proof of (2), ring paragraph;
Section 00YR, sextuples.
Generalized here from the corresponding ring-object construction for étale slices.

Proof: Identify ring sheaves with internal commutative ring objects on both sites,
using the sectionwise-operation identifications. Finite-limit preservation of L
implies finite-product preservation. Apply the ring-only lifted adjunction
to the set adjunction. Compose its left functor with the two inverse identification
functors to obtain Lr, and compose their forgetful comparisons to obtain er.
On the right, the product comparisons for sectionwise precomposition identify each
transported operation with the original operation at the base-changed object.
Consequently the underlying right comparison is a ring isomorphism, natural in the
ring sheaf and site object, to Rr. Transport the lifted unit through this comparison.
Naturality of the transported unit follows from that of the original unit and the
comparisons. The generic lifted-unit formula becomes the displayed equality after
cancelling the inverse-identification components. This constructs only the unit;
no triangle identity or universal property of this unit is asserted here. -/
private theorem ringInverseImageUnit {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : C ⥤ D) [f.IsContinuous J K]
    (hL : PreservesFiniteLimits (f.sheafPullback (Type u) J K)) :
    let b := f
    let L := f.sheafPullback (Type u) J K
    let R := b.sheafPushforwardContinuous (Type (u))
      (J) (K)
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u}
      (J) (K)
    let FrU := sheafForget (D := CommRingCat.{u}) K
    let FrV := sheafForget (D := CommRingCat.{u}) J
    let a := b.sheafAdjunctionContinuous
      (Type (u)) (J)
      (K)
    ∃ (Lr : Sheaf J CommRingCat.{u} ⥤
          Sheaf K CommRingCat.{u})
      (er : Lr ⋙ FrU ≅ FrV ⋙ L) (η : 𝟭 _ ⟶ Lr ⋙ Rr),
      ∀ G, FrV.map (η.app G) = a.unit.app (FrV.obj G) ≫ R.map (er.inv.app G) := by
  let b := f
  let L := f.sheafPullback (Type u) J K
  let R : Sheaf K (Type (u)) ⥤
      Sheaf J (Type (u)) := b.sheafPushforwardContinuous (Type (u))
    (J) (K)
  let Rr : Sheaf K CommRingCat.{u} ⥤
      Sheaf J CommRingCat.{u} :=
    b.sheafPushforwardContinuous CommRingCat.{u}
    (J) (K)
  let FrU := sheafForget (D := CommRingCat.{u}) K
  let FrV := sheafForget (D := CommRingCat.{u}) J
  let a : L ⊣ R := b.sheafAdjunctionContinuous
    (Type (u)) (J)
    (K)
  let : PreservesFiniteLimits L := hL
  let : PreservesFiniteProducts L := ⟨fun n => inferInstance⟩
  obtain ⟨FU, GU, hFU, hGU, hFUGU, hGUFU, opsU⟩ :=
    sheavesAlgebraicStructuresRing_core.{u, u, u} K
  obtain ⟨FV, GV, hFV, hGV, hFVGV, hGVFV, opsV⟩ :=
    sheavesAlgebraicStructuresRing_core.{u, u, u} J
  let : PreservesLimitsOfSize.{0, 0} R := a.rightAdjoint_preservesLimits
  let : PreservesFiniteProducts R := ⟨fun n => inferInstance⟩
  obtain ⟨LF, RF, hLF, hRF, ar, opsL, opsR, homs, units, counits, criteria⟩ :=
    a.liftedCommRingBranch
  let Lr := FV ⋙ LF ⋙ GU
  have he : Lr ⋙ FrU = FrV ⋙ L := by
    change FV ⋙ LF ⋙ GU ⋙ FrU = FrV ⋙ L
    rw [show GU ⋙ FrU = CommRingObjCat.forget _ from hGU]
    rw [hLF]
    change (FV ⋙ CommRingObjCat.forget _) ⋙ L = FrV ⋙ L
    rw [show FV ⋙ CommRingObjCat.forget _ = FrV from hFV]
  let er : Lr ⋙ FrU ≅ FrV ⋙ L := eqToIso he
  obtain ⟨d, hd⟩ := ringDirectImageComparison J K f
    FU GU hFU hGU hGUFU opsU FV GV hFV hGV hGVFV opsV RF hRF opsR
  change ∀ X, FrV.map (d.hom.app X) =
    (eqToIso hGV).hom.app (RF.obj X) ≫ (eqToIso hRF).hom.app X ≫
      R.map ((eqToIso hGU).inv.app X) at hd
  clear opsU opsV opsL opsR homs counits criteria
  let η : 𝟭 _ ⟶ Lr ⋙ Rr :=
    (eqToIso hFVGV).inv ≫ Functor.whiskerLeft FV (Functor.whiskerRight ar.unit GV) ≫
      Functor.whiskerLeft (FV ⋙ LF) d.hom
  refine ⟨Lr, er, η, ?_⟩
  intro G
  change FrV.map (η.app G) = a.unit.app (FrV.obj G) ≫ R.map (er.inv.app G)
  dsimp only [η, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [FrV.map_comp, FrV.map_comp, hd]
  dsimp only [Functor.comp_obj]
  change (FrV.map ((eqToIso hFVGV).inv.app G) ≫
      FrV.map (GV.map (ar.unit.app (FV.obj G)))) ≫
    (eqToIso hGV).hom.app (RF.obj (LF.obj (FV.obj G))) ≫
      (eqToIso hRF).hom.app (LF.obj (FV.obj G)) ≫
        R.map ((eqToIso hGU).inv.app (LF.obj (FV.obj G))) =
    a.unit.app (FrV.obj G) ≫ R.map (er.inv.app G)
  have hn := (eqToIso hGV).hom.naturality (ar.unit.app (FV.obj G))
  change FrV.map (GV.map (ar.unit.app (FV.obj G))) ≫
    (eqToIso hGV).hom.app (RF.obj (LF.obj (FV.obj G))) =
    (eqToIso hGV).hom.app (FV.obj G) ≫
      (CommRingObjCat.forget _).map (ar.unit.app (FV.obj G)) at hn
  rw [Category.assoc, ← Category.assoc (FrV.map (GV.map _)), hn]
  have hstart : FrV.map ((eqToIso hFVGV).inv.app G) ≫
      (eqToIso hGV).hom.app (FV.obj G) = (eqToIso hFV).inv.app G := by
    simp only [eqToIso, eqToHom_app, eqToHom_map, eqToHom_trans]
  simp only [Category.assoc]
  rw [← Category.assoc (FrV.map ((eqToIso hFVGV).inv.app G))
    ((eqToIso hGV).hom.app (FV.obj G)), hstart]
  have hu : (CommRingObjCat.forget _).map (ar.unit.app (FV.obj G)) ≫
      (eqToIso hRF).hom.app (LF.obj (FV.obj G)) =
      a.unit.app (FV.obj G).X ≫ R.map ((eqToIso hLF).inv.app (FV.obj G)) := by
    apply (cancel_mono (R.map ((eqToIso hLF).hom.app (FV.obj G)))).1
    simp only [Category.assoc]
    rw [← R.map_comp, (eqToIso hLF).inv_hom_id_app]
    dsimp only [Functor.comp_obj, Functor.id_obj, CommRingObjCat.forget_obj]
    rw [R.map_id, Category.comp_id]
    exact units (FV.obj G)
  have hn' := a.unit.naturality ((eqToIso hFV).inv.app G)
  change (eqToIso hFV).inv.app G ≫ a.unit.app (FV.obj G).X =
    a.unit.app (FrV.obj G) ≫ R.map (L.map ((eqToIso hFV).inv.app G)) at hn'
  have hend : L.map ((eqToIso hFV).inv.app G) ≫
      (eqToIso hLF).inv.app (FV.obj G) ≫
        (eqToIso hGU).inv.app (LF.obj (FV.obj G)) = er.inv.app G := by
    simp only [er, eqToIso, eqToHom_app, eqToHom_map, eqToHom_trans]
  rw [← Category.assoc ((CommRingObjCat.forget _).map _), hu]
  simp only [Category.assoc]
  rw [← Category.assoc ((eqToIso hFV).inv.app G), hn']
  simp only [Category.assoc, ← R.map_comp]
  rw [hend]


private noncomputable def ringAdd.{uC, vC, w} {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget CommRingCat.{w})]
    (G : Sheaf J CommRingCat.{w}) :
    (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G) :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ @Add.add (G.obj.obj W) inferInstance
       ((prod.fst : (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶
         (sheafForget J |>.obj G)).hom.app W x : G.obj.obj W)
       ((prod.snd : (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶
         (sheafForget J |>.obj G)).hom.app W x : G.obj.obj W))
     naturality := by
       intro W W' f
       ext x
       have hf := ConcreteCategory.congr_hom ((prod.fst : (sheafForget J |>.obj G) ⨯
         (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G)).hom.naturality f) x
       have hs := ConcreteCategory.congr_hom ((prod.snd : (sheafForget J |>.obj G) ⨯
         (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G)).hom.naturality f) x
       dsimp at hf hs ⊢
       rw [hf, hs]
       exact (G.obj.map f).hom.map_add _ _ |>.symm }⟩
private noncomputable def ringMul.{uC, vC, w} {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget CommRingCat.{w})]
    (G : Sheaf J CommRingCat.{w}) :
    (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G) :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ @Mul.mul (G.obj.obj W) inferInstance
       ((prod.fst : (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶
         (sheafForget J |>.obj G)).hom.app W x : G.obj.obj W)
       ((prod.snd : (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶
         (sheafForget J |>.obj G)).hom.app W x : G.obj.obj W))
     naturality := by
       intro W W' f
       ext x
       have hf := ConcreteCategory.congr_hom ((prod.fst : (sheafForget J |>.obj G) ⨯
         (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G)).hom.naturality f) x
       have hs := ConcreteCategory.congr_hom ((prod.snd : (sheafForget J |>.obj G) ⨯
         (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G)).hom.naturality f) x
       dsimp at hf hs ⊢
       rw [hf, hs]
       exact (G.obj.map f).hom.map_mul _ _ |>.symm }⟩
private noncomputable def ringZero.{uC, vC, w} {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget CommRingCat.{w})]
    (G : Sheaf J CommRingCat.{w}) : ⊤_ (Sheaf J (Type w)) ⟶ (sheafForget J |>.obj G) :=
  ⟨{ app := fun W ↦ ↾(fun _ ↦ (0 : G.obj.obj W))
     naturality := by
       intro W W' f
       ext x
       exact (G.obj.map f).hom.map_zero |>.symm }⟩
private noncomputable def ringOne.{uC, vC, w} {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget CommRingCat.{w})]
    (G : Sheaf J CommRingCat.{w}) : ⊤_ (Sheaf J (Type w)) ⟶ (sheafForget J |>.obj G) :=
  ⟨{ app := fun W ↦ ↾(fun _ ↦ (1 : G.obj.obj W))
     naturality := by
       intro W W' f
       ext x
       exact (G.obj.map f).hom.map_one |>.symm }⟩


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
-- Product comparisons and sectionwise operations require repeated functor reduction.
/-- Source: Stacks Project, Proposition 00YV, proof of (2), ring paragraph.
Generalized here from the corresponding ring-object construction for étale slices.

Proof: Put β_F = er_F* followed by the set counit (where er_F* is the component
at Rr F). The unit formula and the right triangle identity imply that the forgotten
ring unit at Rr F, followed by R(β_F), is the identity. For a binary operation,
precompose the desired compatibility of β_F with the isomorphism
L(X × X) → Y × Y obtained from the product comparison and two inverse components
of er, with X the underlying sheaf of Rr F and Y that of Lr(Rr F).
Apply the injective set-adjunction bijection. The adjunct t of this isomorphism has
projections equal to the forgotten ring unit composed with the projections of X × X:
this follows from unit naturality and the projection equations for the comparison.
On sections, replace those projections by the unit applied to each coordinate.
Because the unit is a ring homomorphism, their sum (or product) is the unit of the
sum (or product). Applying β_F now cancels the unit by the preceding identity.
This proves compatibility with addition and multiplication. For zero and one,
precompose with the invertible terminal comparison, apply the same bijection,
and use preservation of the constant by the ring unit and its cancellation by β_F.
The categorical product has all pairs of sections: map the sectionwise Cartesian
tensor product to it by its two projections. The categorical terminal sheaf has
a section at every object: map the singleton Cartesian unit to it. Evaluating the
four operation equalities on these sections gives the ring-homomorphism axioms
for β_F at every site object. Its naturality in the site object is already that of
the underlying sheaf morphism, so these homomorphisms define a ring-sheaf morphism.
Finally naturality of er and of the set counit proves naturality in F. Negation
preservation follows from the ring-homomorphism axioms. No ring adjunction is used. -/
private theorem ringInverseImageCounit {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : C ⥤ D) [f.IsContinuous J K]
    (hL : PreservesFiniteLimits (f.sheafPullback (Type u) J K)) :
    let b := f
    let L := f.sheafPullback (Type u) J K
    let R := b.sheafPushforwardContinuous (Type (u))
      (J) (K)
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u}
      (J) (K)
    let FrU := sheafForget (D := CommRingCat.{u}) K
    let FrV := sheafForget (D := CommRingCat.{u}) J
    let a := b.sheafAdjunctionContinuous
      (Type (u)) (J)
      (K)
    ∀ (Lr : Sheaf J CommRingCat.{u} ⥤
          Sheaf K CommRingCat.{u})
      (er : Lr ⋙ FrU ≅ FrV ⋙ L) (η : 𝟭 _ ⟶ Lr ⋙ Rr),
      (∀ G, FrV.map (η.app G) = a.unit.app (FrV.obj G) ≫ R.map (er.inv.app G)) →
      ∃ ε : Rr ⋙ Lr ⟶ 𝟭 _,
        ∀ F, FrU.map (ε.app F) = er.hom.app (Rr.obj F) ≫ a.counit.app (FrU.obj F) :=
  by
  dsimp only
  intro Lr er η hη
  let b := f
  let L := f.sheafPullback (Type u) J K
  let R : Sheaf K (Type (u)) ⥤
      Sheaf J (Type (u)) := b.sheafPushforwardContinuous _
    (J) (K)
  let Rr : Sheaf K CommRingCat.{u} ⥤
      Sheaf J CommRingCat.{u} := b.sheafPushforwardContinuous _
    (J) (K)
  let FrU := sheafForget (D := CommRingCat.{u}) K
  let FrV := sheafForget (D := CommRingCat.{u}) J
  let a : L ⊣ R := b.sheafAdjunctionContinuous
    (Type (u)) (J)
    (K)
  let : PreservesFiniteLimits L := hL
  let : PreservesFiniteProducts L := ⟨fun _ ↦ inferInstance⟩
  change ∀ G, FrV.map (η.app G) = a.unit.app (FrV.obj G) ≫ R.map (er.inv.app G) at hη
  let β (F : Sheaf K CommRingCat.{u}) :
      FrU.obj (Lr.obj (Rr.obj F)) ⟶ FrU.obj F :=
    er.hom.app (Rr.obj F) ≫ a.counit.app (FrU.obj F)
  have hβ (F : Sheaf K CommRingCat.{u}) :
      FrV.map (η.app (Rr.obj F)) ≫ R.map (β F) = 𝟙 (FrV.obj (Rr.obj F)) := by
    rw [hη]
    change (a.unit.app (FrV.obj (Rr.obj F)) ≫ R.map (er.inv.app (Rr.obj F))) ≫
      R.map (er.hom.app (Rr.obj F) ≫ a.counit.app (FrU.obj F)) = 𝟙 _
    calc
      _ = a.unit.app (FrV.obj (Rr.obj F)) ≫
          R.map ((er.inv.app (Rr.obj F) ≫ er.hom.app (Rr.obj F)) ≫
            a.counit.app (FrU.obj F)) := by simp only [R.map_comp, Category.assoc]
      _ = a.unit.app (FrV.obj (Rr.obj F)) ≫ R.map (a.counit.app (FrU.obj F)) := by
        erw [er.inv_hom_id_app, Category.id_comp]
      _ = 𝟙 _ := a.right_triangle_components (FrU.obj F)
  have hbin (F : Sheaf K CommRingCat.{u})
      (opY : FrU.obj (Lr.obj (Rr.obj F)) ⨯ FrU.obj (Lr.obj (Rr.obj F)) ⟶
        FrU.obj (Lr.obj (Rr.obj F)))
      (opZ : FrU.obj F ⨯ FrU.obj F ⟶ FrU.obj F)
      (op : ∀ S : CommRingCat.{u}, S → S → S)
      (hy : ∀ W x, opY.hom.app W x = op ((Lr.obj (Rr.obj F)).obj.obj W)
        ((prod.fst : _ ⟶ FrU.obj (Lr.obj (Rr.obj F))).hom.app W x)
        ((prod.snd : _ ⟶ FrU.obj (Lr.obj (Rr.obj F))).hom.app W x))
      (hz : ∀ W x, opZ.hom.app W x = op (F.obj.obj W)
        ((prod.fst : _ ⟶ FrU.obj F).hom.app W x)
        ((prod.snd : _ ⟶ FrU.obj F).hom.app W x))
      (hηop : ∀ W x y, (η.app (Rr.obj F)).hom.app W
        (op ((Rr.obj F).obj.obj W) x y) =
        op ((Lr.obj (Rr.obj F)).obj.obj (b.op.obj W))
          ((η.app (Rr.obj F)).hom.app W x) ((η.app (Rr.obj F)).hom.app W y)) :
      opY ≫ β F = prod.map (β F) (β F) ≫ opZ := by
    let X := FrV.obj (Rr.obj F)
    let Y := FrU.obj (Lr.obj (Rr.obj F))
    let q : L.obj (X ⨯ X) ⟶ Y ⨯ Y :=
      prodComparison L X X ≫ prod.map (er.inv.app (Rr.obj F)) (er.inv.app (Rr.obj F))
    have : IsIso q := by dsimp [q]; infer_instance
    let t : X ⨯ X ⟶ R.obj (Y ⨯ Y) := a.homEquiv _ _ q
    have ht (p : X ⨯ X ⟶ X) (p' : Y ⨯ Y ⟶ Y)
        (hp : q ≫ p' = L.map p ≫ er.inv.app (Rr.obj F)) :
        t ≫ R.map p' = p ≫ FrV.map (η.app (Rr.obj F)) := by
      change (a.unit.app (X ⨯ X) ≫ R.map q) ≫ R.map p' = _
      have hn : a.unit.app (X ⨯ X) ≫ R.map (L.map p) = p ≫ a.unit.app X :=
        a.unit_naturality p
      rw [Category.assoc, ← R.map_comp, hp, R.map_comp, ← Category.assoc,
        hn, Category.assoc, ← hη]
    have hf := ht prod.fst prod.fst (by
      dsimp only [q]
      rw [Category.assoc, prod.map_fst, ← Category.assoc, Limits.prodComparison_fst])
    have hs := ht prod.snd prod.snd (by
      dsimp only [q]
      rw [Category.assoc, prod.map_snd, ← Category.assoc, Limits.prodComparison_snd])
    apply (cancel_epi q).1
    apply (a.homEquiv _ _).injective
    change a.unit.app (X ⨯ X) ≫ R.map (q ≫ opY ≫ β F) =
      a.unit.app (X ⨯ X) ≫ R.map (q ≫ prod.map (β F) (β F) ≫ opZ)
    simp only [R.map_comp, ← Category.assoc]
    change (t ≫ R.map opY) ≫ R.map (β F) =
      (t ≫ R.map (prod.map (β F) (β F))) ≫ R.map opZ
    ext W x
    have hf' := types_congr_hom
      (congrArg (fun k : X ⨯ X ⟶ R.obj Y ↦ k.hom.app W) hf) x
    have hs' := types_congr_hom
      (congrArg (fun k : X ⨯ X ⟶ R.obj Y ↦ k.hom.app W) hs) x
    have hb (z : X.obj.obj W) := types_congr_hom
      (congrArg (fun k : X ⟶ X ↦ k.hom.app W) (hβ F)) z
    change (β F).hom.app (b.op.obj W) (opY.hom.app (b.op.obj W) (t.hom.app W x)) =
      opZ.hom.app (b.op.obj W)
        ((prod.map (β F) (β F)).hom.app (b.op.obj W) (t.hom.app W x))
    rw [hy, hz]
    have hpf := types_congr_hom
      (congrArg (fun k : Y ⨯ Y ⟶ FrU.obj F ↦ k.hom.app (b.op.obj W))
        (prod.map_fst (β F) (β F))) (t.hom.app W x)
    have hps := types_congr_hom
      (congrArg (fun k : Y ⨯ Y ⟶ FrU.obj F ↦ k.hom.app (b.op.obj W))
        (prod.map_snd (β F) (β F))) (t.hom.app W x)
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      types_comp_apply] at hpf hps
    rw [hpf, hps]
    change (β F).hom.app (b.op.obj W)
        (op ((Lr.obj (Rr.obj F)).obj.obj (b.op.obj W))
          ((prod.fst : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x))
          ((prod.snd : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x))) =
      op (F.obj.obj (b.op.obj W))
        ((β F).hom.app (b.op.obj W)
          ((prod.fst : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x)))
        ((β F).hom.app (b.op.obj W)
          ((prod.snd : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x)))
    change (prod.fst : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x) =
      (η.app (Rr.obj F)).hom.app W
        ((prod.fst : X ⨯ X ⟶ X).hom.app W x) at hf'
    change (prod.snd : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x) =
      (η.app (Rr.obj F)).hom.app W
        ((prod.snd : X ⨯ X ⟶ X).hom.app W x) at hs'
    change ∀ z, (β F).hom.app (b.op.obj W) ((η.app (Rr.obj F)).hom.app W z) = z at hb
    rw [hf', hs', ← hηop]
    exact (hb _).trans (congrArg₂ (op (F.obj.obj (b.op.obj W))) (hb _).symm (hb _).symm)
  have hadd (F : Sheaf K CommRingCat.{u}) :
      ringAdd _ (Lr.obj (Rr.obj F)) ≫ β F =
        prod.map (β F) (β F) ≫ ringAdd _ F := by
    apply hbin F _ _ (fun S x y ↦ x + y) (by intros; rfl) (by intros; rfl)
    intro W x y
    exact ((η.app (Rr.obj F)).hom.app W).hom.map_add x y
  have hmul (F : Sheaf K CommRingCat.{u}) :
      ringMul _ (Lr.obj (Rr.obj F)) ≫ β F =
        prod.map (β F) (β F) ≫ ringMul _ F := by
    apply hbin F _ _ (fun S x y ↦ x * y) (by intros; rfl) (by intros; rfl)
    intro W x y
    exact ((η.app (Rr.obj F)).hom.app W).hom.map_mul x y
  have hcst (F : Sheaf K CommRingCat.{u})
      (opY : ⊤_ (Sheaf K (Type (u))) ⟶
        FrU.obj (Lr.obj (Rr.obj F)))
      (opZ : ⊤_ (Sheaf K (Type (u))) ⟶ FrU.obj F)
      (c : ∀ S : CommRingCat.{u}, S)
      (hy : ∀ W x, opY.hom.app W x = c ((Lr.obj (Rr.obj F)).obj.obj W))
      (hz : ∀ W x, opZ.hom.app W x = c (F.obj.obj W))
      (hηc : ∀ W, (η.app (Rr.obj F)).hom.app W (c ((Rr.obj F).obj.obj W)) =
        c ((Lr.obj (Rr.obj F)).obj.obj (b.op.obj W))) : opY ≫ β F = opZ := by
    apply (cancel_epi (Limits.terminalComparison L)).1
    apply (a.homEquiv _ _).injective
    let t := a.unit.app (⊤_ (Sheaf J (Type (u)))) ≫
      R.map (Limits.terminalComparison L)
    change a.unit.app _ ≫ R.map (Limits.terminalComparison L ≫ opY ≫ β F) =
      a.unit.app _ ≫ R.map (Limits.terminalComparison L ≫ opZ)
    simp only [R.map_comp, ← Category.assoc]
    change (t ≫ R.map opY) ≫ R.map (β F) = t ≫ R.map opZ
    ext W x
    change (β F).hom.app (b.op.obj W) (opY.hom.app (b.op.obj W) (t.hom.app W x)) =
      opZ.hom.app (b.op.obj W) (t.hom.app W x)
    rw [hy, hz, ← hηc]
    exact types_congr_hom
      (congrArg (fun k : FrV.obj (Rr.obj F) ⟶ FrV.obj (Rr.obj F) ↦ k.hom.app W)
        (hβ F)) (c ((Rr.obj F).obj.obj W))
  have hzero (F : Sheaf K CommRingCat.{u}) :
      ringZero _ (Lr.obj (Rr.obj F)) ≫ β F = ringZero _ F := by
    apply hcst F _ _ (fun _ ↦ 0) (by intros; rfl) (by intros; rfl)
    intro W
    exact ((η.app (Rr.obj F)).hom.app W).hom.map_zero
  have hone (F : Sheaf K CommRingCat.{u}) :
      ringOne _ (Lr.obj (Rr.obj F)) ≫ β F = ringOne _ F := by
    apply hcst F _ _ (fun _ ↦ 1) (by intros; rfl) (by intros; rfl)
    intro W
    exact ((η.app (Rr.obj F)).hom.app W).hom.map_one
  have coords (Y : Sheaf K (Type (u)))
      (W : Dᵒᵖ) (x y : Y.obj.obj W) :
      ∃ s : (Y ⨯ Y).obj.obj W,
        (prod.fst : Y ⨯ Y ⟶ Y).hom.app W s = x ∧
        (prod.snd : Y ⨯ Y ⟶ Y).hom.app W s = y := by
    let c : Y ⊗ Y ⟶ Y ⨯ Y := prod.lift
      (CartesianMonoidalCategory.fst Y Y) (CartesianMonoidalCategory.snd Y Y)
    refine ⟨c.hom.app W (x, y), ?_, ?_⟩
    · exact types_congr_hom (congrArg (fun k : Y ⊗ Y ⟶ Y ↦ k.hom.app W)
        (prod.lift_fst (CartesianMonoidalCategory.fst Y Y)
          (CartesianMonoidalCategory.snd Y Y))) (x, y)
    · exact types_congr_hom (congrArg (fun k : Y ⊗ Y ⟶ Y ↦ k.hom.app W)
        (prod.lift_snd (CartesianMonoidalCategory.fst Y Y)
          (CartesianMonoidalCategory.snd Y Y))) (x, y)
  have hbinary_sections (F : Sheaf K CommRingCat.{u})
      (opY : FrU.obj (Lr.obj (Rr.obj F)) ⨯ FrU.obj (Lr.obj (Rr.obj F)) ⟶
        FrU.obj (Lr.obj (Rr.obj F)))
      (opZ : FrU.obj F ⨯ FrU.obj F ⟶ FrU.obj F)
      (op : ∀ S : CommRingCat.{u}, S → S → S)
      (hy : ∀ W x, opY.hom.app W x = op ((Lr.obj (Rr.obj F)).obj.obj W)
        ((prod.fst : _ ⟶ FrU.obj (Lr.obj (Rr.obj F))).hom.app W x)
        ((prod.snd : _ ⟶ FrU.obj (Lr.obj (Rr.obj F))).hom.app W x))
      (hz : ∀ W x, opZ.hom.app W x = op (F.obj.obj W)
        ((prod.fst : _ ⟶ FrU.obj F).hom.app W x)
        ((prod.snd : _ ⟶ FrU.obj F).hom.app W x))
      (he : opY ≫ β F = prod.map (β F) (β F) ≫ opZ)
      (W : Dᵒᵖ) (x y : (Lr.obj (Rr.obj F)).obj.obj W) :
      (β F).hom.app W (op ((Lr.obj (Rr.obj F)).obj.obj W) x y) =
        op (F.obj.obj W) ((β F).hom.app W x) ((β F).hom.app W y) := by
    let Y := FrU.obj (Lr.obj (Rr.obj F))
    obtain ⟨s, hs₁, hs₂⟩ := coords Y W x y
    have hp₁ := types_congr_hom
      (congrArg (fun k : Y ⨯ Y ⟶ FrU.obj F ↦ k.hom.app W)
        (prod.map_fst (β F) (β F))) s
    have hp₂ := types_congr_hom
      (congrArg (fun k : Y ⨯ Y ⟶ FrU.obj F ↦ k.hom.app W)
        (prod.map_snd (β F) (β F))) s
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      types_comp_apply] at hp₁ hp₂
    have hh := types_congr_hom
      (congrArg (fun k : Y ⨯ Y ⟶ FrU.obj F ↦ k.hom.app W) he) s
    change (β F).hom.app W (opY.hom.app W s) =
      opZ.hom.app W ((prod.map (β F) (β F)).hom.app W s) at hh
    rw [hy, hz, hp₁, hp₂, hs₁, hs₂] at hh
    exact hh
  have hconstant_sections (F : Sheaf K CommRingCat.{u})
      (opY : ⊤_ (Sheaf K (Type (u))) ⟶
        FrU.obj (Lr.obj (Rr.obj F)))
      (opZ : ⊤_ (Sheaf K (Type (u))) ⟶ FrU.obj F)
      (c : ∀ S : CommRingCat.{u}, S)
      (hy : ∀ W x, opY.hom.app W x = c ((Lr.obj (Rr.obj F)).obj.obj W))
      (hz : ∀ W x, opZ.hom.app W x = c (F.obj.obj W))
      (he : opY ≫ β F = opZ) (W : Dᵒᵖ) :
      (β F).hom.app W (c ((Lr.obj (Rr.obj F)).obj.obj W)) = c (F.obj.obj W) := by
    let t : 𝟙_ (Sheaf K (Type (u))) ⟶
        ⊤_ (Sheaf K (Type (u))) := terminal.from _
    have hh := types_congr_hom
      (congrArg (fun k : ⊤_ (Sheaf K (Type (u))) ⟶
        FrU.obj F ↦ k.hom.app W) he) (t.hom.app W PUnit.unit)
    change (β F).hom.app W (opY.hom.app W _) = opZ.hom.app W _ at hh
    rw [hy, hz] at hh
    exact hh
  let ε : Rr ⋙ Lr ⟶ 𝟭 _ := {
    app := fun F ↦ ⟨{
      app := fun W ↦ CommRingCat.ofHom {
        toFun := (β F).hom.app W
        map_zero' := hconstant_sections F _ _ (fun _ ↦ 0)
          (by intros; rfl) (by intros; rfl) (hzero F) W
        map_one' := hconstant_sections F _ _ (fun _ ↦ 1)
          (by intros; rfl) (by intros; rfl) (hone F) W
        map_add' := hbinary_sections F _ _ (fun S x y ↦ x + y)
          (by intros; rfl) (by intros; rfl) (hadd F) W
        map_mul' := hbinary_sections F _ _ (fun S x y ↦ x * y)
          (by intros; rfl) (by intros; rfl) (hmul F) W }
      naturality := by
        intro W W' g
        ext x
        exact types_congr_hom ((β F).hom.naturality g) x }⟩
    naturality := by
      intro F F' g
      apply FrU.map_injective
      change FrU.map (Lr.map (Rr.map g)) ≫ β F' = β F ≫ FrU.map g
      dsimp only [β]
      have he : FrU.map (Lr.map (Rr.map g)) ≫ er.hom.app (Rr.obj F') =
          er.hom.app (Rr.obj F) ≫ L.map (FrV.map (Rr.map g)) :=
        er.hom.naturality (Rr.map g)
      rw [← Category.assoc, he]
      change (er.hom.app (Rr.obj F) ≫ L.map (R.map (FrU.map g))) ≫
          a.counit.app (FrU.obj F') =
        (er.hom.app (Rr.obj F) ≫ a.counit.app (FrU.obj F)) ≫ FrU.map g
      have hn : L.map (R.map (FrU.map g)) ≫ a.counit.app (FrU.obj F') =
          a.counit.app (FrU.obj F) ≫ FrU.map g := a.counit_naturality (FrU.map g)
      rw [Category.assoc, hn, Category.assoc] }
  refine ⟨ε, ?_⟩
  intro F
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Sites and Sheaves, Proposition 00YV, ring paragraph;
Section 00YR, rings as sextuples.
Generalized here from the corresponding ring-object construction for étale slices.

Proof: Apply the ring clause of `sheaves_algebraicStructures_objects` to both sites.
Finite-limit preservation implies finite-product preservation for the set inverse
image. Apply `Adjunction.liftedCommRingBranch` to its adjunction.
Compose the left and right lifted functors with the inverse functors between ring
sheaves and internal ring objects. The transported right functor is isomorphic to
sectionwise direct image: its underlying sheaf is precomposition with base change,
and the five transported operations are the original operations evaluated at each
base-changed object. The sectionwise identification is a ring homomorphism and is
natural in the sheaf. Transport the adjunction along this right-functor isomorphism.
Compose the left forgetful comparisons to obtain `er`. The generic lift's hom-set
identity, transported through the strict inverse functors and the right identification,
is precisely the asserted identity. This construction needs no assertion about the
left operation formulas; those will be deduced separately from this identity. -/
private theorem ringInverseImageAdjunction {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : C ⥤ D) [f.IsContinuous J K]
    (hL : PreservesFiniteLimits (f.sheafPullback (Type u) J K)) :
    let b := f
    let L := f.sheafPullback (Type u) J K
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u}
      (J) (K)
    let FrU := sheafForget (D := CommRingCat.{u}) K
    let FrV := sheafForget (D := CommRingCat.{u}) J
    let a := b.sheafAdjunctionContinuous
      (Type (u)) (J)
      (K)
    ∃ (Lr : Sheaf J CommRingCat.{u} ⥤
          Sheaf K CommRingCat.{u})
      (ar : Lr ⊣ Rr) (er : Lr ⋙ FrU ≅ FrV ⋙ L),
        ∀ (G : Sheaf J CommRingCat.{u})
            (F : Sheaf K CommRingCat.{u}) (h : Lr.obj G ⟶ F),
          FrV.map (ar.homEquiv G F h) =
            a.homEquiv (FrV.obj G) (FrU.obj F) (er.inv.app G ≫ FrU.map h) := by
  let b := f
  let L := f.sheafPullback (Type u) J K
  let R : Sheaf K (Type (u)) ⥤
      Sheaf J (Type (u)) := b.sheafPushforwardContinuous (Type (u))
    (J) (K)
  let Rr : Sheaf K CommRingCat.{u} ⥤
      Sheaf J CommRingCat.{u} :=
    b.sheafPushforwardContinuous CommRingCat.{u}
    (J) (K)
  let FrU := sheafForget (D := CommRingCat.{u}) K
  let FrV := sheafForget (D := CommRingCat.{u}) J
  let a : L ⊣ R := b.sheafAdjunctionContinuous
    (Type (u)) (J)
    (K)
  obtain ⟨Lr, er, η, hη⟩ := ringInverseImageUnit J K f hL
  obtain ⟨ε, hε⟩ := ringInverseImageCounit J K f hL Lr er η hη
  change ∀ G, FrV.map (η.app G) =
    a.unit.app (FrV.obj G) ≫ R.map (er.inv.app G) at hη
  change ∀ F, FrU.map (ε.app F) =
    er.hom.app (Rr.obj F) ≫ a.counit.app (FrU.obj F) at hε
  let ar : Lr ⊣ Rr := {
    unit := η
    counit := ε
    left_triangle_components := by
      intro G
      apply FrU.map_injective
      rw [FrU.map_comp, FrU.map_id, hε]
      change FrU.map (Lr.map (η.app G)) ≫
        er.hom.app (Rr.obj (Lr.obj G)) ≫ a.counit.app (FrU.obj (Lr.obj G)) = 𝟙 _
      have hn : FrU.map (Lr.map (η.app G)) ≫ er.hom.app (Rr.obj (Lr.obj G)) =
          er.hom.app G ≫ L.map (FrV.map (η.app G)) := er.hom.naturality (η.app G)
      rw [← Category.assoc, hn]
      change er.hom.app G ≫ L.map (FrV.map (η.app G)) ≫
        a.counit.app (FrU.obj (Lr.obj G)) = 𝟙 _
      have hc : L.map (R.map (er.inv.app G)) ≫ a.counit.app (FrU.obj (Lr.obj G)) =
          a.counit.app (L.obj (FrV.obj G)) ≫ er.inv.app G :=
        a.counit_naturality (er.inv.app G)
      rw [hη, L.map_comp]
      simp only [Category.assoc]
      rw [hc]
      calc
        _ = er.hom.app G ≫ (L.map (a.unit.app (FrV.obj G)) ≫
            a.counit.app (L.obj (FrV.obj G))) ≫ er.inv.app G := by
          simp only [Category.assoc]
        _ = er.hom.app G ≫ er.inv.app G := by
          rw [a.left_triangle_components]
          exact congrArg (fun k ↦ k ≫ er.inv.app G)
            (Category.comp_id (er.hom.app G))
        _ = 𝟙 _ := er.hom_inv_id_app G
    right_triangle_components := by
      intro F
      apply FrV.map_injective
      rw [FrV.map_comp, FrV.map_id, hη]
      change (a.unit.app (FrV.obj (Rr.obj F)) ≫ R.map (er.inv.app (Rr.obj F))) ≫
        R.map (FrU.map (ε.app F)) = 𝟙 _
      rw [hε]
      calc
        _ = a.unit.app (FrV.obj (Rr.obj F)) ≫
            R.map ((er.inv.app (Rr.obj F) ≫ er.hom.app (Rr.obj F)) ≫
              a.counit.app (FrU.obj F)) := by simp only [R.map_comp, Category.assoc]
        _ = a.unit.app (FrV.obj (Rr.obj F)) ≫ R.map (a.counit.app (FrU.obj F)) := by
          rw [er.inv_hom_id_app]
          exact congrArg (fun k ↦ a.unit.app (FrV.obj (Rr.obj F)) ≫ R.map k)
            (Category.id_comp (a.counit.app (FrU.obj F)))
        _ = 𝟙 _ := a.right_triangle_components (FrU.obj F) }
  refine ⟨Lr, ar, er, ?_⟩
  intro G F h
  rw [ar.homEquiv_apply, FrV.map_comp, hη]
  change (a.unit.app (FrV.obj G) ≫ R.map (er.inv.app G)) ≫ R.map (FrU.map h) =
    a.homEquiv (FrV.obj G) (FrU.obj F) (er.inv.app G ≫ FrU.map h)
  rw [a.homEquiv_apply, R.map_comp, Category.assoc]


/-- The chosen ring inverse image has the normalized underlying set inverse image. -/
private theorem ringPullbackForgetNormalized
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : C ⥤ D) [f.IsContinuous J K]
    [PreservesFiniteLimits (f.sheafPullback (Type u) J K)] :
    ∃ e : f.sheafPullback CommRingCat.{u} J K ⋙ sheafForget K ≅
        sheafForget J ⋙ f.sheafPullback (Type u) J K,
      ∀ (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
        (h : (f.sheafPullback CommRingCat.{u} J K).obj A ⟶ B),
        (sheafForget J).map ((f.sheafAdjunctionContinuous CommRingCat.{u} J K).homEquiv A B h) =
          (f.sheafAdjunctionContinuous (Type u) J K).homEquiv
            ((sheafForget J).obj A) ((sheafForget K).obj B)
            (e.inv.app A ≫ (sheafForget K).map h) := by
  obtain ⟨Lr, ar, er, hr⟩ := ringInverseImageAdjunction J K f inferInstance
  let adj := f.sheafAdjunctionContinuous CommRingCat.{u} J K
  let q := ar.leftAdjointUniq adj
  let e := Functor.isoWhiskerRight q.symm (sheafForget K) ≪≫ er
  refine ⟨e, ?_⟩
  intro A B h
  have hq : ar.homEquiv A B (q.hom.app A ≫ h) = adj.homEquiv A B h := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
    rw [← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]
  rw [← hq, hr, Functor.map_comp]
  congr 1


variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J] (V : D)
  [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]

/-- The direct-image square for ring sheaves is identity on sections.
Source: Stacks Tag 03CF
(blueprint: lem-weil-pbc-slice-commRing-pullback-isIso). -/
def sliceCommRingPushforwardIso :
    u.sheafPushforwardContinuous CommRingCat.{u} K J ⋙ K.overPullback CommRingCat.{u} V ≅
      J.overPullback CommRingCat.{u} (u.obj V) ⋙
        (Over.post (X := V) u).sheafPushforwardContinuous CommRingCat.{u}
          (K.over V) (J.over (u.obj V)) :=
  NatIso.ofComponents (fun G ↦ ObjectProperty.isoMk _ (Iso.refl _))

/-- The ring inverse-image comparison, defined as the inverse mate.
Source: Stacks Tags 03CF and 04J0
(blueprint: lem-weil-pbc-slice-commRing-pullback-isIso). -/
def sliceCommRingPullbackMap :
    K.overPullback CommRingCat.{u} V ⋙
        (Over.post (X := V) u).sheafPullback CommRingCat.{u}
          (K.over V) (J.over (u.obj V)) ⟶
      u.sheafPullback CommRingCat.{u} K J ⋙
        J.overPullback CommRingCat.{u} (u.obj V) :=
  ((mateEquiv (u.sheafAdjunctionContinuous CommRingCat.{u} K J)
    ((Over.post (X := V) u).sheafAdjunctionContinuous CommRingCat.{u}
      (K.over V) (J.over (u.obj V)))).symm
        (TwoSquare.mk _ _ _ _ (sliceCommRingPushforwardIso (K := K) (J := J) u V).hom)).natTrans

/-- The unit equation characterizes the canonical ring inverse mate.
Source: Stacks Tags 03CF and 04J0
(blueprint: lem-weil-pbc-slice-commRing-pullback-isIso). -/
theorem sliceCommRingPullbackMap_unit (R : Sheaf K CommRingCat.{u}) :
    (K.overPullback CommRingCat.{u} V).map
        ((u.sheafAdjunctionContinuous CommRingCat.{u} K J).unit.app R) ≫
      (sliceCommRingPushforwardIso (K := K) (J := J) u V).hom.app
        ((u.sheafPullback CommRingCat.{u} K J).obj R) =
    ((Over.post (X := V) u).sheafAdjunctionContinuous CommRingCat.{u}
        (K.over V) (J.over (u.obj V))).unit.app (R.over V) ≫
      ((Over.post (X := V) u).sheafPushforwardContinuous CommRingCat.{u}
        (K.over V) (J.over (u.obj V))).map
          ((sliceCommRingPullbackMap (K := K) (J := J) u V).app R) := by
  exact unit_mateEquiv_symm
    (u.sheafAdjunctionContinuous CommRingCat.{u} K J)
    ((Over.post (X := V) u).sheafAdjunctionContinuous CommRingCat.{u}
      (K.over V) (J.over (u.obj V)))
    (TwoSquare.mk _ _ _ _ (sliceCommRingPushforwardIso (K := K) (J := J) u V).hom) R

/-- A ring comparison satisfying the canonical unit equation is the inverse mate.
Source: Stacks Tags 03CF and 04J0, uniqueness under the sheaf adjunction
(blueprint: lem-weil-pbc-slice-commRing-pullback-isIso). -/
theorem sliceCommRingPullbackMap_eq_of_unit
    (t : K.overPullback CommRingCat.{u} V ⋙
        (Over.post (X := V) u).sheafPullback CommRingCat.{u}
          (K.over V) (J.over (u.obj V)) ⟶
      u.sheafPullback CommRingCat.{u} K J ⋙
        J.overPullback CommRingCat.{u} (u.obj V))
    (ht : ∀ R : Sheaf K CommRingCat.{u},
      ((Over.post (X := V) u).sheafAdjunctionContinuous CommRingCat.{u}
        (K.over V) (J.over (u.obj V))).unit.app (R.over V) ≫
        ((Over.post (X := V) u).sheafPushforwardContinuous CommRingCat.{u}
          (K.over V) (J.over (u.obj V))).map (t.app R) =
      (K.overPullback CommRingCat.{u} V).map
          ((u.sheafAdjunctionContinuous CommRingCat.{u} K J).unit.app R) ≫
        (sliceCommRingPushforwardIso (K := K) (J := J) u V).hom.app
          ((u.sheafPullback CommRingCat.{u} K J).obj R)) :
    t = sliceCommRingPullbackMap (K := K) (J := J) u V := by
  apply NatTrans.ext
  funext R
  apply (((Over.post (X := V) u).sheafAdjunctionContinuous CommRingCat.{u}
    (K.over V) (J.over (u.obj V))).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ht]
  exact sliceCommRingPullbackMap_unit (K := K) (J := J) u V R

/-- The comparison carries the adjunct of a ring map to its sectionwise restriction.
Source: Stacks Tag 04J0
(blueprint: lem-weil-pbc-slice-commRing-pullback-isIso). -/
theorem sliceCommRingPullbackMap_adjunct
    {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
    (a : R ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj S) :
    ((Over.post (X := V) u).sheafAdjunctionContinuous CommRingCat.{u}
      (K.over V) (J.over (u.obj V))).homEquiv (R.over V) (S.over (u.obj V))
        ((sliceCommRingPullbackMap (K := K) (J := J) u V).app R ≫
          (J.overPullback CommRingCat.{u} (u.obj V)).map
            (((u.sheafAdjunctionContinuous CommRingCat.{u} K J).homEquiv R S).symm a)) =
      (K.overPullback CommRingCat.{u} V).map a ≫
        (sliceCommRingPushforwardIso (K := K) (J := J) u V).hom.app S := by
  let adj := u.sheafAdjunctionContinuous CommRingCat.{u} K J
  let adjV := (Over.post (X := V) u).sheafAdjunctionContinuous CommRingCat.{u}
    (K.over V) (J.over (u.obj V))
  let jV := K.overPullback CommRingCat.{u} V
  let jU := J.overPullback CommRingCat.{u} (u.obj V)
  let b := sliceCommRingPushforwardIso (K := K) (J := J) u V
  let l := sliceCommRingPullbackMap (K := K) (J := J) u V
  have hl := sliceCommRingPullbackMap_unit (K := K) (J := J) u V R
  rw [Adjunction.homEquiv_unit]
  change adjV.unit.app (jV.obj R) ≫
      ((Over.post (X := V) u).sheafPushforwardContinuous CommRingCat.{u}
        (K.over V) (J.over (u.obj V))).map
          (l.app R ≫ jU.map ((adj.homEquiv R S).symm a)) = _
  change jV.map (adj.unit.app R) ≫ b.hom.app _ =
    adjV.unit.app (jV.obj R) ≫
      ((Over.post (X := V) u).sheafPushforwardContinuous CommRingCat.{u}
        (K.over V) (J.over (u.obj V))).map (l.app R) at hl
  rw [Functor.map_comp, ← Category.assoc, ← hl]
  have hn := b.hom.naturality ((adj.homEquiv R S).symm a)
  change jV.map ((u.sheafPushforwardContinuous CommRingCat.{u} K J).map
      ((adj.homEquiv R S).symm a)) ≫ b.hom.app S =
    b.hom.app _ ≫
      ((Over.post (X := V) u).sheafPushforwardContinuous CommRingCat.{u}
        (K.over V) (J.over (u.obj V))).map
          (jU.map ((adj.homEquiv R S).symm a)) at hn
  rw [Category.assoc, ← hn]
  change jV.map (adj.unit.app R) ≫
      jV.map ((u.sheafPushforwardContinuous CommRingCat.{u} K J).map
        ((adj.homEquiv R S).symm a)) ≫ b.hom.app S = _
  rw [← jV.map_comp_assoc]
  have ha := (adj.homEquiv R S).apply_symm_apply a
  rw [Adjunction.homEquiv_unit] at ha
  change adj.unit.app R ≫ (u.sheafPushforwardContinuous CommRingCat.{u} K J).map
    ((adj.homEquiv R S).symm a) = a at ha
  exact congrArg (fun k ↦ jV.map k ≫ b.hom.app S) ha

/-- The canonical inverse-image comparison is invertible for sheaves of rings.
Source: Stacks Project, Sites, Tag 03CF, and Modules on Sites, Tag 04J0.
(blueprint: lem-weil-pbc-slice-commRing-pullback-isIso).

Proof: Use the canonical set-sheaf comparison and finite-limit preservation on the
localized site. Construct the product-preserving lift of the set-sheaf adjunction to
commutative ring objects, transport through the sectionwise ring-object equivalences,
and identify it with the chosen ring-sheaf adjunction by uniqueness of left adjoints.
The resulting forgetful comparison satisfies the specified hom-set identity. Apply
that identity globally and on the localized site. Injectivity of the localized set
adjunction and the two unit equations identify the forgotten ring comparison with
the set comparison conjugated by those isomorphisms. Its components are invertible;
the forgetful functor reflects isomorphisms. -/
theorem sliceCommRingPullbackMap_isIso
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)] :
    IsIso (sliceCommRingPullbackMap (K := K) (J := J) u V) := by
  let := sliceSetPullback_preservesFiniteLimits (K := K) (J := J) u V
  obtain ⟨eg, hg⟩ := ringPullbackForgetNormalized K J u
  obtain ⟨ev, hv⟩ := ringPullbackForgetNormalized (K.over V) (J.over (u.obj V))
    (Over.post (X := V) u)
  rw [NatTrans.isIso_iff_isIso_app]
  intro R
  let F := sheafForget (J.over (u.obj V)) (D := CommRingCat.{u})
  suffices hi : IsIso (F.map ((sliceCommRingPullbackMap (K := K) (J := J) u V).app R)) by
    exact isIso_of_reflects_iso _ F
  have hm : ev.inv.app (R.over V) ≫
      F.map ((sliceCommRingPullbackMap (K := K) (J := J) u V).app R) =
      (sliceSetPullbackMap (K := K) (J := J) u V).app ((sheafForget K).obj R) ≫
        (J.overPullback (Type u) (u.obj V)).map (eg.inv.app R) := by
    apply (((Over.post (X := V) u).sheafAdjunctionContinuous (Type u)
      (K.over V) (J.over (u.obj V))).homEquiv _ _).injective
    rw [← hv]
    rw [Adjunction.homEquiv_unit]
    rw [← sliceCommRingPullbackMap_unit (K := K) (J := J) u V R]
    have hgu := hg R ((u.sheafPullback CommRingCat.{u} K J).obj R) (𝟙 _)
    erw [Adjunction.homEquiv_id, Functor.map_id, Category.comp_id] at hgu
    rw [Adjunction.homEquiv_unit] at hgu
    change (K.overPullback (Type u) V).map
        ((sheafForget K).map ((u.sheafAdjunctionContinuous CommRingCat.{u} K J).unit.app R)) = _
    rw [hgu, Functor.map_comp]
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
    erw [← sliceSetPullbackMap_unit (K := K) (J := J) u V ((sheafForget K).obj R)]
    rfl
  have : IsIso (sliceSetPullbackMap (K := K) (J := J) u V) :=
    sliceSetPullbackMap_isIso (K := K) (J := J) u V
  have : IsIso (ev.inv.app (R.over V) ≫
      F.map ((sliceCommRingPullbackMap (K := K) (J := J) u V).app R)) := by
    rw [hm]
    infer_instance
  exact IsIso.of_isIso_comp_left (ev.inv.app (R.over V))
    (F.map ((sliceCommRingPullbackMap (K := K) (J := J) u V).app R))

end CategoryTheory
