/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Scalar extension and terminal evaluation

Source: HRS, proof following (4.4); Stacks Project, Modules on Sites, 03D1--03D3.
-/

@[expose] public section
set_option autoImplicit false
universe u v uC uD vC vD
open CategoryTheory Opposite
namespace CategoryTheory

/-- A normalized evaluation comparison identifies the two scalar-extension left adjoints.
Source: HRS, proof following (4.4)
(blueprint: lem-zl-module-terminal-scalar-comparison).

Proof: restrict a module along the site functor and the structural ring map.
Evaluation at c is evaluation at F(c) with restricted scalars. The restriction map
along the given isomorphism F(c) ≅ d is invertible. Its semilinearity becomes
R-linearity by the normalization of e. These maps form a natural isomorphism of
the two right adjoints. Compose the first scalar-extension adjunction with the
module adjunction, then use uniqueness of left adjoints. -/
theorem module_terminal_scalar_comparison
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    (A : Sheaf J RingCat.{u}) (B : Sheaf K RingCat.{u})
    (φ : A ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj B)
    (c : C) (d : D) (t : F.obj c ≅ d)
    (e : A.obj.obj (op c) ≅ B.obj.obj (op d))
    (he : e.hom = φ.hom.app (op c) ≫ B.obj.map t.inv.op)
    (E : SheafOfModules.{v} A ⥤ SheafOfModules.{v} B)
    (adj : E ⊣ SheafOfModules.pushforward φ)
    (R : Type u) [Ring R] (a : R →+* A.obj.obj (op c))
    (FS : ModuleCat.{v} R ⥤ SheafOfModules.{v} A)
    (FV : ModuleCat.{v} R ⥤ SheafOfModules.{v} B)
    (aS : FS ⊣ SheafOfModules.evaluation A (op c) ⋙ ModuleCat.restrictScalars a)
    (aV : FV ⊣ SheafOfModules.evaluation B (op d) ⋙
      ModuleCat.restrictScalars (e.hom.hom.comp a)) :
    Nonempty (FS ⋙ E ≅ FV) := by
  classical
  let θ : SheafOfModules.pushforward φ ⋙
      (SheafOfModules.evaluation A (op c) ⋙ ModuleCat.restrictScalars a) ≅
      SheafOfModules.evaluation B (op d) ⋙
        ModuleCat.restrictScalars (e.hom.hom.comp a) :=
    NatIso.ofComponents (fun M ↦
      { hom := ModuleCat.ofHom
          (X := (ModuleCat.restrictScalars a).obj
            ((SheafOfModules.evaluation A (op c)).obj
              ((SheafOfModules.pushforward φ).obj M)))
          (Y := (ModuleCat.restrictScalars (e.hom.hom.comp a)).obj (M.val.obj (op d)))
          { toFun := M.val.map t.inv.op
            map_add' := map_add _
            map_smul' := by
              intro r x
              change M.val.obj (op (F.obj c)) at x
              change M.val.map t.inv.op (((φ.hom.app (op c)).hom (a r)) • x) =
                (e.hom.hom (a r)) • M.val.map t.inv.op x
              rw [M.val.map_smul]
              have hh := congrArg (fun k : A.obj.obj (op c) ⟶ B.obj.obj (op d) ↦
                k.hom (a r)) he
              exact congrArg (fun q ↦ q • M.val.map t.inv.op x) hh.symm }
        inv := ModuleCat.ofHom
          (X := (ModuleCat.restrictScalars (e.hom.hom.comp a)).obj (M.val.obj (op d)))
          (Y := (ModuleCat.restrictScalars a).obj
            ((SheafOfModules.evaluation A (op c)).obj
              ((SheafOfModules.pushforward φ).obj M)))
          { toFun := M.val.map t.hom.op
            map_add' := map_add _
            map_smul' := by
              intro r x
              change M.val.obj (op d) at x
              change M.val.map t.hom.op ((e.hom.hom (a r)) • x) =
                ((φ.hom.app (op c)).hom (a r)) • M.val.map t.hom.op x
              rw [M.val.map_smul]
              have hh := congrArg (fun k : A.obj.obj (op c) ⟶ B.obj.obj (op d) ↦
                k.hom (a r)) he
              rw [hh]
              have hi := congrArg (fun k : B.obj.obj (op (F.obj c)) ⟶
                B.obj.obj (op (F.obj c)) ↦ k.hom ((φ.hom.app (op c)).hom (a r)))
                (B.obj.mapIso t.op).inv_hom_id
              exact congrArg (fun q ↦ q • M.val.map t.hom.op x) hi }
        hom_inv_id := by
          ext x
          change M.val.map t.hom.op (M.val.map t.inv.op x) = x
          exact congrArg (fun k : M.val.presheaf.obj (op (F.obj c)) ⟶
            M.val.presheaf.obj (op (F.obj c)) ↦ k x)
            (M.val.presheaf.mapIso t.op).inv_hom_id
        inv_hom_id := by
          ext x
          change M.val.map t.inv.op (M.val.map t.hom.op x) = x
          exact congrArg (fun k : M.val.presheaf.obj (op d) ⟶
            M.val.presheaf.obj (op d) ↦ k x)
            (M.val.presheaf.mapIso t.op).hom_inv_id })
      (by
        intro M N f
        ext x
        exact (PresheafOfModules.naturality_apply f.val t.inv.op x).symm)
  exact ⟨((aS.comp adj).ofNatIsoRight θ).leftAdjointUniq aV⟩

end CategoryTheory
