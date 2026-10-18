/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.CategoryTheory.LocalCoefficientLocalization
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Internal Hom from a countable free unit sum

Source: Stacks Project, algebraization.tex, Tag 0997, proof of lemma-hom-from-Af.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory


private noncomputable def opFreeSumIsLimit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    IsLimit (Fan.mk (op (SheafOfModules.free (R := localCoefficientRings R) (ULift.{u} ℕ)))
      (fun n : ℕ ↦ (SheafOfModules.ιFree (R := localCoefficientRings R) (ULift.up.{u} n)).op)) := by
  refine Fan.IsLimit.mk _
    (fun s ↦ (Sigma.desc fun n : ULift.{u} ℕ ↦ (s.proj n.down).unop).op) ?_ ?_
  · intro s n
    apply Quiver.Hom.unop_inj
    change SheafOfModules.ιFree (ULift.up n) ≫
      Sigma.desc (fun n : ULift.{u} ℕ ↦ (s.proj n.down).unop) = _
    exact Sigma.ι_desc _ _
  · intro s m hm
    apply Quiver.Hom.unop_inj
    apply Sigma.hom_ext
    rintro ⟨n⟩
    have h := congrArg Quiver.Hom.unop (hm n)
    change SheafOfModules.ιFree (ULift.up n) ≫ m.unop = (s.proj n).unop at h
    change SheafOfModules.ιFree (ULift.up n) ≫ m.unop =
      SheafOfModules.ιFree (ULift.up n) ≫ Sigma.desc _
    exact h.trans (Sigma.ι_desc
      (fun k : ULift.{u} ℕ ↦ (s.proj k.down).unop) (ULift.up.{u} n)).symm

/-- Internal Hom from a countable free unit sum has the indicated product projections.

Source: Stacks Project, Tag 0997, proof of lemma-hom-from-Af.
(blueprint: lem-weil-pbc-countable-free-internal-hom-product).

Proof: The opposite free coproduct cone is a limit cone, including the reindexing
from lifted natural numbers to natural numbers. The tensor-Hom adjunction is natural
in its tensor variable, so defines a parametrized adjunction. Tensoring on either
side preserves coproducts: tensoring on the left is a left adjoint and braiding
identifies it with tensoring on the right. Consequently internal Hom in its source
variable preserves this limit cone. Its factors are internal Hom from the unit;
evaluation at 1 identifies these with N. Transporting the limit property along
these isomorphisms gives exactly the stated projections. No finiteness of the free
rank, flatness of N, or exactness of countable products is required. -/
theorem countableFree_internalHom_product
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (N : ringedSiteModules.{u} (localCoefficientRings R)) :
    Nonempty (IsLimit (Fan.mk (SheafOfModules.homObj (R := R)
      (SheafOfModules.free (ULift.{u} ℕ)) N)
      (fun n : ℕ ↦ SheafOfModules.homObjMap.{u, u, u, u} (R := R)
        (SheafOfModules.ιFree (R := localCoefficientRings R) (ULift.up.{u} n)) (𝟙 N) ≫
        (SheafOfModules.homObjUnitIso (R := R) N).hom))) := by
  let A := ringedSiteModules.{u} (localCoefficientRings R)
  let : MonoidalCategory A := SheafOfModules.monoidalCategory R
  let : SymmetricCategory A := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed (R := R)
  let H := (SheafOfModules.homFunctor R).flip.obj N
  let adj := ParametrizedAdjunction.mk'
    (F := MonoidalCategory.curriedTensor A) (G := SheafOfModules.homFunctor R)
    (fun M ↦ SheafOfModules.tensorHomAdjunction R M)
    (fun {X Y} f {T N} g ↦ by
      simp only [SheafOfModules.tensorHomAdjunction,
        Adjunction.mkOfHomEquiv_homEquiv]
      exact SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := R) f g)
  have : PreservesLimitsOfShape (Discrete ℕ) H :=
    adj.preservesLimitsOfShape_flip_obj _ N
  obtain ⟨h⟩ : Nonempty (IsLimit (Fan.mk
      (H.obj (op (SheafOfModules.free (R := localCoefficientRings R) (ULift.{u} ℕ))))
      (fun n : ℕ ↦ H.map
        (SheafOfModules.ιFree (R := localCoefficientRings R) (ULift.up.{u} n)).op))) :=
    ⟨isLimitFanMkObjOfIsLimit H
    (fun _ : ℕ ↦ op (SheafOfModules.unit (localCoefficientRings R))) _
    (opFreeSumIsLimit R)⟩
  dsimp only [H, Functor.flip, SheafOfModules.homFunctor] at h
  simp only [Quiver.Hom.unop_op] at h
  refine ⟨?_⟩
  let e := SheafOfModules.homObjUnitIso (R := R) N
  refine Fan.IsLimit.mk _ (fun s ↦ h.lift
    (Fan.mk s.pt (fun n ↦ s.proj n ≫ e.inv))) ?_ ?_
  · intro s n
    simp only [fan_mk_proj]
    have hf := h.fac (Fan.mk s.pt (fun n ↦ s.proj n ≫ e.inv)) (Discrete.mk n)
    simpa only [Fan.mk_π_app, Fan.mk_pt, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun k ↦ k ≫ e.hom) hf
  · intro s m hm
    apply h.hom_ext
    rintro ⟨n⟩
    have hf := h.fac (Fan.mk s.pt (fun n ↦ s.proj n ≫ e.inv)) (Discrete.mk n)
    simp only [Fan.mk_π_app, Fan.mk_pt] at hf
    simp only [Fan.mk_π_app]
    rw [hf]
    apply (cancel_mono e.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, fan_mk_proj] using hm n


end CategoryTheory
