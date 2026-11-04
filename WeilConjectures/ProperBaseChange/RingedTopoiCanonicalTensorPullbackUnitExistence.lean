/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement


@[expose] public section
universe u v u' v'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))
open scoped ChangeOfRings

set_option maxHeartbeats 600000 in
-- Check the transported rank-one action and its sectionwise linear equivalences.
private theorem inverseImage_unit_iso :
    ∃ e : unit (RingedTensor.ringSheaf RI) ≅
        I.modules.obj (unit (RingedTensor.ringSheaf R)),
      (RingedTensor.underlying RI).map e.hom =
        I.ringUnderlying.inv ≫ I.moduleUnderlying.inv.app
          (unit (RingedTensor.ringSheaf R)) := by
  let U := unit (RingedTensor.ringSheaf R)
  let Z := (RingedTensor.underlying R).obj U
  let one : Z ⟶ Z := ⟨{ app := fun W ↦ ↾(fun _ ↦ (1 : R.obj.obj W))
                        naturality := by
                          intro W V f
                          ext x
                          exact (map_one (R.obj.map f).hom).symm }⟩
  let e : (RingedTensor.underlying RI).obj (I.modules.obj U) ≅
      (sheafCompose JD (CategoryTheory.forget CommRingCat.{u})).obj RI :=
    I.moduleUnderlying.app U ≪≫ I.ringUnderlying
  let g (W : Dᵒᵖ) (r : RI.obj.obj W) : (I.modules.obj U).val.obj W :=
    e.inv.hom.app W r
  have hf (W : Dᵒᵖ) (r : RI.obj.obj W) : g W r = r • g W 1 := by
    let t := I.ringUnderlying.inv.hom.app W r
    have ht : I.ringUnderlying.hom.hom.app W t = r :=
      congrArg (fun f ↦ f.hom.app W r) I.ringUnderlying.inv_hom_id
    have ho := I.ringOne Z one (fun _ _ ↦ rfl) W t
    have hi := congrArg (I.ringUnderlying.inv.hom.app W) ho
    have hc (x : (uInv.obj Z).obj.obj W) :
        I.ringUnderlying.inv.hom.app W (I.ringUnderlying.hom.hom.app W x) = x :=
      congrArg (fun f ↦ f.hom.app W x) I.ringUnderlying.hom_inv_id
    simp only [id_eq] at hi
    rw [hc] at hi
    let m (x : (uInv.obj Z).obj.obj W) : (I.modules.obj U).val.obj W :=
      (I.moduleUnderlying.inv.app U).hom.app W x
    have hm : m t = (I.ringUnderlying.hom.hom.app W t : RI.obj.obj W) •
        m ((uInv.map one).hom.app W t) := by
      have h := I.moduleSMul U Z (𝟙 Z) one (𝟙 Z)
        (fun W x ↦ (mul_one (show R.obj.obj W from x)).symm) W t
      erw [uInv.map_id] at h
      exact h
    erw [ht, hi] at hm
    exact hm
  let eW (W : Dᵒᵖ) : RI.obj.obj W ≃ₗ[RI.obj.obj W] (I.modules.obj U).val.obj W :=
    { toEquiv := (((sheafToPresheaf JD (Type u)).mapIso e).app W).toEquiv.symm
      map_add' := by
        intro r s
        change g W (r + s) = g W r + g W s
        rw [hf W (r + s), hf W r, hf W s, add_smul]
      map_smul' := by
        intro r s
        change g W (r * s) = r • g W s
        rw [hf W (r * s), hf W s, mul_smul] }
  let ep : (unit (RingedTensor.ringSheaf RI)).val ≅ (I.modules.obj U).val :=
    PresheafOfModules.isoMk (fun W ↦ (eW W).toModuleIso) (by
      intro W V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      exact congrArg (fun k ↦ k r) (e.inv.hom.naturality f))
  refine ⟨(fullyFaithfulForget _).preimageIso ep, ?_⟩
  rfl

private theorem scalarExtension_unit_iso :
    ∃ e : (RingedTensor.tensorFunctor c).obj (unit (RingedTensor.ringSheaf RI)) ≅
        unit (RingedTensor.ringSheaf S),
      ∀ (W : Dᵒᵖ) (r : RI.obj.obj W),
        e.hom.val.app W
          ((RingedTensor.tensorUnit c (unit (RingedTensor.ringSheaf RI))).hom.app W r) =
            c.hom.app W r := by
  let A := RingedTensor.ringSheaf RI
  let B := RingedTensor.ringSheaf S
  let F := PresheafOfModules.sheafification (𝟙 B.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)
  let eW (W : Dᵒᵖ) :
      (changeOfRingsPresheaf.{u, u, u} c (unit A)).obj W ≅ (unit B).val.obj W := by
    let := (c.hom.app W).hom.toAlgebra
    exact (TensorProduct.AlgebraTensorModule.rid (RI.obj.obj W)
      (S.obj.obj W) (S.obj.obj W)).toModuleIso
  let ep : changeOfRingsPresheaf.{u, u, u} c (unit A) ≅ (unit B).val :=
    PresheafOfModules.isoMk eW (by
      intro W V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul s r =>
        change S.obj.obj W at s
        change RI.obj.obj W at r
        change (eW V).hom ((changeOfRingsPresheaf c (unit A)).map f
          (s ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom] r)) =
            S.obj.map f ((eW W).hom (s ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom] r))
        erw [tensorRestriction_tmul]
        change c.hom.app V (RI.obj.map f r) * S.obj.map f s =
          S.obj.map f (c.hom.app W r * s)
        rw [map_mul]
        exact congrArg (fun a ↦ a * S.obj.map f s)
          (congrArg (fun k ↦ k r) (c.hom.naturality f)))
  let e : (RingedTensor.tensorFunctor c).obj (unit A) ≅ unit B :=
    F.mapIso ep ≪≫ asIso (adj.counit.app (unit B))
  refine ⟨e, ?_⟩
  intro W r
  erw [tensorUnit_apply]
  let v := (1 : S.obj.obj W) ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom] r
  have hn := adj.unit.naturality ep.hom
  have hh := congrArg (fun f ↦ f.app W v) hn
  have ht := congrArg (fun f ↦ f.app W (c.hom.app W r))
    (adj.right_triangle_components (unit B))
  change (adj.counit.app (unit B)).val.app W
    ((F.map ep.hom).val.app W ((adj.unit.app _).app W v)) = _
  refine (congrArg ((adj.counit.app (unit B)).val.app W) hh.symm).trans ?_
  change (adj.counit.app (unit B)).val.app W
    ((adj.unit.app (unit B).val).app W ((eW W).hom v)) = _
  have hv : (eW W).hom v = c.hom.app W r := by
    change c.hom.app W r * 1 = c.hom.app W r
    exact mul_one _
  rw [hv]
  exact ht

-- Transport scalar extension and evaluate the comparison on generalized unit tensors.
end SheafOfModules
