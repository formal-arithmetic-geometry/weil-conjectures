/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Localization of the small pro-etale site at a weakly etale object

Source: Stacks Project, Tags 098K, 094T, 0951, 00XZ, 04IX and 09AE
(blueprint: lem-weil-proetale-weakly-etale-localization).
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.ProEt

private theorem module_transport
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) [e.inverse.IsDenseSubsite K J]
    (R : Sheaf J RingCat.{u + 1}) (S : Sheaf K RingCat.{u + 1})
    (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R) :
    ∃ q : SheafOfModules.{u + 1} R ≌ SheafOfModules.{u + 1} S,
      q.functor ⋙ SheafOfModules.forget _ =
        SheafOfModules.forget _ ⋙ PresheafOfModules.pushforward (F := e.inverse) c.hom.hom := by
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S :=
    { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
        Functor.whiskerLeft e.functor.op c.inv.hom }
  have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      ψ.hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map _ =
      (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
    rw [Category.assoc]
    have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
    have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
        c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
    change R.obj.map (e.unitInv.app U.unop).op =
      R.obj.map (e.unitInv.app U.unop).op ≫
        (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)
  have H₂ : c.hom.hom ≫ e.inverse.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    change c.hom.hom.app U ≫
      (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
        S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
    rw [Category.assoc]
    have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
    change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
      c.inv.hom.app U =
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
        S.obj.map (e.counitInv.app U.unop).op at hn
    rw [← hn]
    have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp]
      simp
    rw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
    change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
    have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
      (Category.id_comp (c.inv.hom.app U))).trans hc
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  refine ⟨SheafOfModules.pushforwardPushforwardEquivalence e.symm c.hom ψ H₁ H₂, rfl⟩

end AlgebraicGeometry.Scheme.ProEt
