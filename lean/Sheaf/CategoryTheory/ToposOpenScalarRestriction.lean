/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R7
-/
module

public import Sheaf.CategoryTheory.ToposOpenScalarBasic
import all Sheaf.CategoryTheory.ToposOpenUnitIsIso
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction

/-! # Ordinary coefficient comparison on the element site -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace SheafOfModules.ToposOpenScalar
attribute [local instance 0] hasSheafCompose_of_preservesMulticospan
attribute [local instance 20000] hasSheafCompose_of_preservesLimitsOfSize
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (A : Sheaf J (Type u)) {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)

private abbrev scalarRestriction {D : Type u} [SmallCategory D]
    {K : GrothendieckTopology D} {B T : Sheaf K CommRingCat.{u}} (b : B ⟶ T) :=
  restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map b)

variable
  [HasDerivedCategory.{w}
    (ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J R))]
  [HasDerivedCategory.{w}
    (ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J S))]
  [HasDerivedCategory.{w} (ringedSiteModules.{u}
    (derivedChangeRingIndependentCoefficients (elementTopology A) (presentationElementRing R A)))]
  [HasDerivedCategory.{w} (ringedSiteModules.{u}
    (derivedChangeRingIndependentCoefficients (elementTopology A) (presentationElementRing S A)))]


private theorem scalarAdjunction
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {B T : Sheaf K CommRingCat.{u}} (b : B ⟶ T)
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients K B))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients K T))]
    (E : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} b) :
    ∃ d : E.E ⊣ scalarRestriction b,
      ∀ (M : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients K B))
        (N : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients K T))
        (g : E.E.obj M ⟶ N) (U : Dᵒᵖ) (m : M.val.obj U),
      (d.homEquiv M N g).val.app U m = g.val.app U (tensorSection b E M U m 1) := by
  obtain ⟨_, _, h⟩ := sheafRingCoefficientOrdinaryAdjunction b
  obtain ⟨d, hd⟩ := h E.E E.obj_eq E.map_eq
  refine ⟨d, ?_⟩
  intro M N g U m
  have he : eqToHom (E.obj_eq M) ≫ (eqToHom (E.obj_eq M).symm ≫ g) = g := by simp
  have hh := hd M N (eqToHom (E.obj_eq M).symm ≫ g) U m
  rw [he] at hh
  exact hh

private theorem tensorSection_hom_ext
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {B T : Sheaf K CommRingCat.{u}} (b : B ⟶ T)
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients K B))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients K T))]
    (E : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} b)
    (M : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients K B))
    (N : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients K T))
    (f g : E.E.obj M ⟶ N)
    (h : ∀ U m, f.val.app U (tensorSection b E M U m 1) =
      g.val.app U (tensorSection b E M U m 1)) : f = g := by
  obtain ⟨d, hd⟩ := scalarAdjunction b E
  apply (d.homEquiv M N).injective
  ext U m
  rw [hd, hd]
  exact h U m

private theorem tensorSection_map
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {B T : Sheaf K CommRingCat.{u}} (b : B ⟶ T)
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients K B))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients K T))]
    (E : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} b)
    {M N : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients K B)}
    (f : M ⟶ N) (U : Dᵒᵖ) (m : M.val.obj U) :
    (E.E.map f).val.app U (tensorSection b E M U m 1) =
      tensorSection b E N U (f.val.app U m) 1 := by
  obtain ⟨d, hd⟩ := scalarAdjunction b E
  have h := d.homEquiv_naturality_left f (𝟙 (E.E.obj N))
  have he := congrArg (fun g ↦ g.val.app U m) h
  rw [Category.comp_id] at he
  change (d.homEquiv _ _ (E.E.map f)).val.app U m =
    (d.homEquiv _ _ (𝟙 (E.E.obj N))).val.app U (f.val.app U m) at he
  simpa only [hd, SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.hom_id,
    LinearMap.id_apply] using he

@[irreducible] private def restrictionTensorIso
    (ET : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a)
    (EV : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} (sliceMap A a))
    (M : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J R)) :
    EV.E.obj ((restriction R A).obj M) ≅ (restriction S A).obj (ET.E.obj M) := by
  haveI := restrictionSheafificationMap_isIso A
    (derivedChangeRingIndependentCoefficients J S) (changeOfRingsPresheaf.{u, u, u} a M)
  exact eqToIso (EV.obj_eq _) ≪≫
    asIso (restrictionSheafificationMap A (derivedChangeRingIndependentCoefficients J S)
      (changeOfRingsPresheaf.{u, u, u} a M)) ≪≫
    (restriction S A).mapIso (eqToIso (ET.obj_eq M).symm)



private theorem restrictionTensorIso_tmul
    (ET : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a)
    (EV : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} (sliceMap A a))
    (M : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (f : A.obj.obj U) (m : M.val.obj U) (t : S.obj.obj U) :
    ((restrictionTensorIso A a ET EV M).hom).val.app (elementObj A U f)
      (tensorSection (sliceMap A a) EV ((restriction R A).obj M)
        (elementObj A U f) m t) = tensorSection a ET M U m t := by
  have h := restrictionSheafificationMap_unit A
    (derivedChangeRingIndependentCoefficients J S) (changeOfRingsPresheaf.{u, u, u} a M)
    (elementObj A U f) (t ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] m)
  unfold restrictionTensorIso tensorSection
  simp only [Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom]
  change ((eqToHom (EV.obj_eq ((restriction R A).obj M)) ≫
    restrictionSheafificationMap A (derivedChangeRingIndependentCoefficients J S)
      (changeOfRingsPresheaf.{u, u, u} a M) ≫
      (restriction S A).map (eqToHom (ET.obj_eq M).symm)).val.app
      (elementObj A U f))
    ((eqToHom (EV.obj_eq ((restriction R A).obj M)).symm).val.app
      (elementObj A U f) _) = _
  change ((eqToHom (EV.obj_eq ((restriction R A).obj M)).symm ≫
    eqToHom (EV.obj_eq ((restriction R A).obj M)) ≫
    restrictionSheafificationMap A (derivedChangeRingIndependentCoefficients J S)
      (changeOfRingsPresheaf.{u, u, u} a M) ≫
      (restriction S A).map (eqToHom (ET.obj_eq M).symm)).val.app
      (elementObj A U f)) _ = _
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  exact congrArg ((eqToHom (ET.obj_eq M).symm).val.app U) h

set_option backward.isDefEq.respectTransparency true in
private def ordinaryRestrictionComparison
    (ET : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a)
    (EV : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} (sliceMap A a)) :
    restriction R A ⋙ EV.E ≅ ET.E ⋙ restriction S A :=
  NatIso.ofComponents (restrictionTensorIso A a ET EV) (by
    intro M N g
    apply tensorSection_hom_ext (sliceMap A a) EV ((restriction R A).obj M)
    intro U m
    obtain ⟨⟨⟨U, f⟩⟩⟩ := U
    change ((restrictionTensorIso A a ET EV N).hom).val.app _
        ((EV.E.map ((restriction R A).map g)).val.app _
          (tensorSection (sliceMap A a) EV _ _ m 1)) =
      ((ET.E.map g).val.app U)
        (((restrictionTensorIso A a ET EV M).hom).val.app _
          (tensorSection (sliceMap A a) EV _ _ m 1))
    rw [tensorSection_map]
    change ((restrictionTensorIso A a ET EV N).hom).val.app (elementObj A U f)
      (tensorSection (sliceMap A a) EV ((restriction R A).obj N)
        (elementObj A U f) (g.val.app U m) 1) = _
    erw [restrictionTensorIso_tmul, restrictionTensorIso_tmul, tensorSection_map]
    rfl)

/-- Scalar extension commutes with element-site restriction on its actual pure tensors.
Source: Stacks 03EL and 04IE (blueprint: lem-pur-topos-open-scalar-restriction).

Proof: Restriction is precomposition along the continuous cocontinuous element
projection, so it commutes with sheafification. Apply that comparison to the
sectionwise scalar-extension presheaf. Its sheafification-unit equation gives the
pure-tensor formula. Naturality follows by checking maps on the scalar-adjunction
unit generators; the scalar Hom bijection makes those generators jointly epic. -/
theorem exists_toposOpenScalarRestriction
    (ET : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a)
    (EV : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} (sliceMap A a)) :
    ∃ rho : ET.E ⋙ restriction S A ≅ restriction R A ⋙ EV.E,
      ∀ (M : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J R))
        (U : Cᵒᵖ) (f : A.obj.obj U) (m : M.val.obj U) (t : S.obj.obj U),
        (rho.hom.app M).val.app (elementObj A U f) (tensorSection a ET M U m t) =
          tensorSection (sliceMap A a) EV ((restriction R A).obj M)
            (elementObj A U f) m t := by
  let e := ordinaryRestrictionComparison A a ET EV
  refine ⟨e.symm, ?_⟩
  intro M U f m t
  have h := restrictionTensorIso_tmul A a ET EV M U f m t
  apply_fun ((e.inv.app M).val.app (elementObj A U f)) at h
  change ((e.hom.app M ≫ e.inv.app M).val.app (elementObj A U f)) _ = _ at h
  rw [Iso.hom_inv_id_app] at h
  simpa only [Iso.symm_hom, SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply]
    using h.symm

end SheafOfModules.ToposOpenScalar
