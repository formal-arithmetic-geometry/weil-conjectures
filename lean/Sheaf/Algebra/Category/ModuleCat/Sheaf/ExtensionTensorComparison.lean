/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M6
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Restricted scalar extension as a sheaf tensor product -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- The section formula for the scalar-extension unit, using the existing tensor
sheafification. The equality identifies the supplied presentation of the extension object.
Source: Stacks Project, Modules on Sites, Tag 03EK
(blueprint: lem-weil-pbc-scalar-localization-underlying-telescope). -/
def scalarLocalizationTelescopeUnitSections
    {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S)
    (M : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (e : N = SheafOfModules.changeOfRings φ M)
    (η : M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj N) : Prop :=
  ∀ (V : Cᵒᵖ) (x : M.val.obj V),
    (η ≫ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).map (eqToHom e)).val.app V x =
      (toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app V
        ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x)

end CategoryTheory

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {R S : Sheaf J CommRingCat.{u}}

attribute [local instance] monoidalCategory

private def restrictedTensorPresheafIso (φ : R ⟶ S)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
      (unit.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val ⊗ M.val ≅
      (PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
          (changeOfRingsPresheaf.{u, u, u} φ M) := by
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · let ρ := (φ.hom.app V).hom
    let T := TensorProduct (R.obj.obj V)
      ((ModuleCat.restrictScalars ρ).obj (ModuleCat.of (S.obj.obj V) (S.obj.obj V)))
      (M.val.obj V)
    change ModuleCat.of (R.obj.obj V) T ≅
      (ModuleCat.restrictScalars ρ).obj (ModuleCat.of (S.obj.obj V) T)
    exact (LinearEquiv.refl (R.obj.obj V) T).toModuleIso
  · intro V W f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul s m =>
      change S.obj.map f s ⊗ₜ[R.obj.obj W, (φ.hom.app W).hom] M.val.map f m =
        changeOfRingsMap φ M f (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)
      exact (Classical.choose_spec (exists_changeOfRingsMap φ M f) s m).symm

section
variable {R₀ B₀ : Sheaf J RingCat.{u}}

private noncomputable def restrictionSheafificationComparison
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{u} B₀.obj) :
    (PresheafOfModules.sheafification (𝟙 R₀.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj P) ⟶
        (restrictScalars α).obj
          ((PresheafOfModules.sheafification (𝟙 B₀.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R₀.obj)).symm
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P))

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem restrictionSheafificationComparison_isIso
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{u} B₀.obj) :
    IsIso (restrictionSheafificationComparison α P) := by
  rw [← isIso_iff_of_reflects_iso _ (toSheaf R₀)]
  have he : (toSheaf R₀).map (restrictionSheafificationComparison α P) = 𝟙 _ := by
    unfold restrictionSheafificationComparison
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
    apply ((CategoryTheory.sheafificationAdjunction
      J AddCommGrpCat.{u}).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    change (PresheafOfModules.toPresheaf B₀.obj).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P) =
        CategoryTheory.toSheafify J P.presheaf
    exact PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app _ _
  rw [he]
  infer_instance

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem restrictionSheafificationComparison_unit
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{u} B₀.obj)
    (W : Cᵒᵖ) (x : P.obj W) :
    (restrictionSheafificationComparison α P).val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 R₀.obj)).unit.app
          ((PresheafOfModules.restrictScalars α.hom).obj P)).app W x) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P).app W x := by
  have h := (PresheafOfModules.sheafificationHomEquiv
    (P := (PresheafOfModules.restrictScalars α.hom).obj P)
    (F := (restrictScalars α).obj
      ((PresheafOfModules.sheafification (𝟙 B₀.obj)).obj P))
    (𝟙 R₀.obj)).apply_symm_apply
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P))
  exact congrArg (fun k ↦ (k.app W) x) h

end

/-- The canonical map from the presheaf tensor to the underlying sheaf tensor.
Source: Stacks Project, Modules on Sites, Tag 03EK.
(blueprint: lem-weil-pbc-extension-tensor-comparison). -/
def tensorPresheafUnit
    (M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    M.val ⊗ N.val ⟶ ((monoidalCategory R).tensorObj M N).val :=
  (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app _ ≫
      (tensorObjIsoSheafification M N).inv.val

set_option maxHeartbeats 50000 in
-- Mixed tensor coefficient structures require additional elaboration.
/-- Restricted extension of scalars is tensoring with the restricted target ring.
Source: Stacks Project, Modules on Sites, Tag 03EK.
(blueprint: lem-weil-pbc-extension-tensor-comparison).

Proof: the presheaf tensor of the restricted target ring with M has exactly the
same section modules as restricted sectionwise scalar extension. Both restriction
maps send s tensor m to the tensor of the two restrictions, so the identity maps
form an isomorphism. Sheafify it over R. Restriction commutes with sheafification:
after forgetting to abelian sheaves the comparison is the identity of the same
sheafification, and forgetting reflects isomorphisms. Compose with the canonical
tensor-sheafification comparison. Naturality of the sheafification unit gives the
pure-tensor formula. No flatness or localization assumption is used. -/
theorem exists_extensionTensorComparison (φ : R ⟶ S)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ∃ e : (monoidalCategory R).tensorObj
        ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (unit.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) M ≅
        (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (changeOfRings.{u, u, u} φ M),
      ∀ (V : Cᵒᵖ) (s : S.obj.obj V) (m : M.val.obj V),
        e.hom.val.app V
          ((tensorPresheafUnit
            ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
              (unit.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) M).app V
            ((show ((restrictScalars.{u}
                ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
                  (unit.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val.obj V
              from s) ⊗ₜ[R.obj.obj V] m)) =
        (toSheafify J (changeOfRingsPresheaf.{u, u, u} φ M).presheaf).app V
          (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m) := by
  let N := (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
    (unit.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  let P := changeOfRingsPresheaf.{u, u, u} φ M
  let SR := PresheafOfModules.sheafification.{u}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let eP := restrictedTensorPresheafIso φ M
  have := restrictionSheafificationComparison_isIso
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P
  let e := tensorObjIsoSheafification N M ≪≫ SR.mapIso eP ≪≫
    asIso (restrictionSheafificationComparison
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P)
  have he : (tensorObjIsoSheafification N M).inv ≫ e.hom =
      SR.map eP.hom ≫ restrictionSheafificationComparison
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P := by
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
    simp only [Iso.inv_hom_id_assoc]
  clear_value e
  refine ⟨e, ?_⟩
  intro V s m
  have hn := adj.unit.naturality eP.hom
  have hn' := congrArg (fun k ↦ (k.app V)
    ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m)) hn
  have hr' := restrictionSheafificationComparison_unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P V
    (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)
  change ((tensorPresheafUnit N M ≫ e.hom.val).app V)
    ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m) = _
  unfold tensorPresheafUnit
  rw [Category.assoc]
  change ((adj.unit.app (N.val ⊗ M.val) ≫
    ((tensorObjIsoSheafification N M).inv ≫ e.hom).val).app V) _ = _
  rw [he]
  change (restrictionSheafificationComparison
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P).val.app V
    ((SR.map eP.hom).val.app V
      ((adj.unit.app (N.val ⊗ M.val)).app V
        ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m))) = _
  change (adj.unit.app ((PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj P)).app V
        (eP.hom.app V ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m)) =
      (SR.map eP.hom).val.app V ((adj.unit.app (N.val ⊗ M.val)).app V
        ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m)) at hn'
  exact (congrArg ((restrictionSheafificationComparison
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P).val.app V) hn'.symm).trans hr'

/-- A concrete tensor-unit isomorphism, normalized on every local pure tensor.
Source: Stacks Project, Tag 03EK
(blueprint: lem-weil-pbc-extension-tensor-comparison). -/
def regularTensorIso
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (monoidalCategory R).tensorObj
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) M ≅ M :=
  tensorObjIsoSheafification _ M ≪≫
    (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).mapIso (λ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit).app M

/-- Pure tensor sections commute with maps of the first factor.
Source: Stacks Project, Tag 03EK
(blueprint: lem-weil-pbc-extension-tensor-comparison). -/
theorem tensorPresheafUnit_naturality
    {L L' : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : L ⟶ L')
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    tensorPresheafUnit L M ≫ (f ▷ M).val =
      (f.val ▷ M.val) ≫ tensorPresheafUnit L' M := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  have h : (tensorObjIsoSheafification L M).inv ≫ f ▷ M =
      (PresheafOfModules.sheafification
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
          (f.val ▷ M.val) ≫ (tensorObjIsoSheafification L' M).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← whiskerRight_tensorObjIsoSheafification_hom,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold tensorPresheafUnit
  rw [Category.assoc, ← comp_val, h, comp_val, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ (tensorObjIsoSheafification L' M).inv.val)
    (adj.unit.naturality (f.val ▷ M.val)).symm

set_option maxHeartbeats 50000 in
-- Elaborating the tensor unitor requires additional coefficient comparisons.
/-- The inverse regular tensor unitor sends a section to the local tensor of one with it.
Source: Stacks Project, Tag 03EK
(blueprint: lem-weil-pbc-extension-tensor-comparison). -/
theorem regularTensorIso_inv_apply
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : Cᵒᵖ) (x : M.val.obj V) :
    (regularTensorIso M).inv.val.app V x =
      (tensorPresheafUnit (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) M).app V
        ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  have : IsIso adj.counit := by dsimp [adj]; infer_instance
  let e := (asIso adj.counit).app M
  let f := (SheafOfModules.forget _).mapIso e
  have hc : e.inv.val = adj.unit.app M.val := by
    apply (cancel_mono f.hom).1
    change e.inv.val ≫ e.hom.val = adj.unit.app M.val ≫ e.hom.val
    have h := adj.right_triangle_components M
    have hi := congrArg SheafOfModules.Hom.val e.inv_hom_id
    exact hi.trans h.symm
  have hn := adj.unit.naturality (λ_ M.val).inv
  have h := congrArg (fun f ↦ f.app V x) hn
  simp only [regularTensorIso, Iso.trans_inv, Functor.mapIso_inv, comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [hc]
  simp only [Functor.id_map, Functor.comp_map,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at h
  erw [← h]
  rfl

end SheafOfModules
