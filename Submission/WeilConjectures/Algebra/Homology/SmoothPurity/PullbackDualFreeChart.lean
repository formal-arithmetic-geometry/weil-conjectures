/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.PullbackPairingTransfer
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomOver
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Adjunction.Additive
import Submission.WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Finite-free chart calculation for the pulled dual

Source: Stacks Project, Modules on Sites, Tags 03EL, 03EO and 0GMX.
(blueprint: lem-pur-ringed-site-pullback-dual-free-chart)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v w}}
  (N : PresheafOfModules.{max u v w} (R ⋙ forget₂ _ _))

/-- A section `n` of `N` over `U` gives the morphism `R|_U ⟶ N|_U`, `r ↦ r • n`. -/
private noncomputable def chart_homObjUnitInvApp {U : C} (n : N.obj (op U)) :
    (restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj N :=
  (unitHomEquiv ((restrictOver R U).obj N)).symm
    (sectionsMk (fun W ↦ N.map W.unop.hom.op n) fun {W W'} f ↦ by
      change N.map f.unop.left.op (N.map W.unop.hom.op n) = N.map W'.unop.hom.op n
      rw [← map_comp_apply, ← op_comp, Over.w])

private lemma chart_map_id_apply' {X : Cᵒᵖ} (x : N.obj X) : N.map (𝟙 X) x = x := by
  rw [map_id]
  rfl

private lemma chart_homObjUnitInvApp_app_one {U : C} (n : N.obj (op U)) :
    (chart_homObjUnitInvApp N n).app (op (Over.mk (𝟙 U))) (1 : R.obj (op U)) = n :=
  (congrArg (fun s ↦ s.val (op (Over.mk (𝟙 U))))
    ((unitHomEquiv ((restrictOver R U).obj N)).apply_symm_apply _)).trans
      ((N.congr_map_apply op_id n).trans (N.chart_map_id_apply' n))

/-- The sections of `homObj R N` over `X` are the sections of `N` over `X`. -/
private noncomputable def chart_homObjUnitIsoApp (X : Cᵒᵖ) : (homObj (unit _) N).obj X ≅ N.obj X :=
    { hom := ConcreteCategory.ofHom
        { toFun φ := φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj (op X.unop))
          map_add' _ _ := rfl
          map_smul' r φ := by
            refine (restrictOver_smul_app_apply r φ _ _).trans ?_
            change R.map (𝟙 _) r • _ = _
            rw [R.map_id]
            rfl }
      inv := ConcreteCategory.ofHom
        { toFun n := chart_homObjUnitInvApp N n
          map_add' n n' := hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
            (M₂ := (restrictOver R X.unop).obj N) fun W ↦ by
              ext
              change (1 : R.obj (op W.unop.left)) •
                  (show N.obj (op W.unop.left) from N.map W.unop.hom.op (n + n')) =
                (1 : R.obj (op W.unop.left)) •
                    (show N.obj (op W.unop.left) from N.map W.unop.hom.op n) +
                  (1 : R.obj (op W.unop.left)) •
                    (show N.obj (op W.unop.left) from N.map W.unop.hom.op n')
              rw [map_add, smul_add]
          map_smul' r n := hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
            (M₂ := (restrictOver R X.unop).obj N) fun W ↦ by
              ext
              change (1 : R.obj (op W.unop.left)) •
                  (show N.obj (op W.unop.left) from N.map W.unop.hom.op (r • n)) =
                R.map W.unop.hom.op r • (1 : R.obj (op W.unop.left)) •
                  (show N.obj (op W.unop.left) from N.map W.unop.hom.op n)
              rw [one_smul, one_smul, N.map_smul]
              rfl }
      hom_inv_id := by
        ext φ : 2
        refine hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
          (M₂ := (restrictOver R X.unop).obj N) fun W ↦ ?_
        refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
        change (1 : R.obj (op W.unop.left)) • (show N.obj (op W.unop.left) from
          N.map W.unop.hom.op (φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj (op X.unop)))) =
            φ.app W (1 : R.obj (op W.unop.left))
        rw [one_smul]
        refine (naturality_apply φ
          (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 X.unop)).op
          (1 : R.obj (op X.unop))).symm.trans ?_
        exact congrArg (φ.app W) (unit_map_one (R := R ⋙ forget₂ _ _) W.unop.hom.op)
      inv_hom_id := by
        ext n
        exact chart_homObjUnitInvApp_app_one N n }

/-- **The internal hom out of the unit.** `homObj R N ≅ N`: a morphism `R|_U ⟶ N|_U` is
determined by the image of `1`. -/
private noncomputable def chart_homObjUnitIso : homObj (unit _) N ≅ N :=
  isoMk (chart_homObjUnitIsoApp N) fun X Y g ↦ by
    ext φ
    change φ.app (op (Over.mk (𝟙 Y.unop ≫ g.unop))) (1 : R.obj Y) =
      N.map g (φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj X))
    refine (restrictOver_hom_app_congr (M := unit _) (N := N) φ (Category.id_comp g.unop)
      (1 : R.obj Y)).trans (Eq.trans ?_ (naturality_apply φ
        (Over.homMk g.unop (Category.comp_id _) : Over.mk g.unop ⟶ Over.mk (𝟙 X.unop)).op
          (1 : R.obj X)))
    exact congrArg (φ.app _) (unit_map_one (R := R ⋙ forget₂ _ _) g).symm

end PresheafOfModules

namespace SheafOfModules

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  {R : Sheaf J CommRingCat.{max u v w}} {S : Sheaf K CommRingCat.{max u v w}}
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))

section UnitHelpers

private noncomputable def chart_unitHom
    (N : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) : homObj (R := R) (unit _) N ⟶ N :=
  { val := { app := fun X ↦ (PresheafOfModules.chart_homObjUnitIsoApp.{u, v, w}
      (R := R.obj) N.val X).hom
             naturality := (PresheafOfModules.chart_homObjUnitIso.{u, v, w}
               (R := R.obj) N.val).hom.naturality } }

private noncomputable def chart_unitInv
    (N : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) : N ⟶ homObj (R := R) (unit _) N :=
  { val := { app := fun X ↦ (PresheafOfModules.chart_homObjUnitIsoApp.{u, v, w}
      (R := R.obj) N.val X).inv
             naturality := (PresheafOfModules.chart_homObjUnitIso.{u, v, w}
               (R := R.obj) N.val).inv.naturality } }

@[irreducible]
private noncomputable def chart_unitHomIso
    (N : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) : homObj (R := R) (unit _) N ≅ N :=
  { hom := chart_unitHom.{u, v, w} (R := R) N
    inv := chart_unitInv.{u, v, w} (R := R) N
    hom_inv_id := by
      apply hom_ext
      exact (PresheafOfModules.chart_homObjUnitIso.{u, v, w} (R := R.obj) N.val).hom_inv_id
    inv_hom_id := by
      apply hom_ext
      exact (PresheafOfModules.chart_homObjUnitIso.{u, v, w} (R := R.obj) N.val).inv_hom_id }

private lemma chart_unitHomIso_hom_eval
    (N : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : C) (φ : (homObj (R := R) (unit _) N).val.obj (op V)) :
    (chart_unitHomIso.{u, v, w} (R := R) N).hom.val.app (op V) φ =
      φ.app (op (Over.mk (𝟙 V))) (1 : R.obj.obj (op V)) := by
  unfold chart_unitHomIso
  rfl

end UnitHelpers

set_option backward.isDefEq.respectTransparency true

section GlobalComparison

open SheafOfModules.RingedSitePullback
variable [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
  [(pushforward.{max u v w} a).IsRightAdjoint]
  (hcover : CoverPreserving J K U)
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

@[irreducible]
private noncomputable def dualComparison
    (L : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (pullback a).obj (homObj (R := R) L (unit _)) ⟶ homObj (R := S) ((pullback a).obj L) (unit _) :=
  (exists_pullback_pairing_transfer.{u, v, w} (R := R) (S := S) a hcover
    inferInstance L (homObj (R := R) L (unit _)) (𝟙 _)).choose

end GlobalComparison

end SheafOfModules
