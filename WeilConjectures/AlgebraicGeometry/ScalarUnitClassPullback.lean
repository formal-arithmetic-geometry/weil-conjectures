/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarUnitCohomologyCoordinates
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality
import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # Structure-sheaf pullback preserves the degree-zero class of one

## References

* [Stacks Project, Tag 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 01F7](https://stacks.math.columbia.edu/tag/01F7)
* [Stacks Project, Tag 01DZ](https://stacks.math.columbia.edu/tag/01DZ)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

section

open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Sheaf.monoidalCategory HasExt.standard

private theorem augmentation_cocycle {C : Type*} [Category C] [Abelian C]
    {A : C} (I : InjectiveResolution A) :
    CochainComplex.HomComplex.Cocycle.equivHomShift.symm
      (CochainComplex.HomComplex.Cocycle.fromSingleMk
        (I.ι.f 0 ≫ (I.cochainComplexXIso 0 0 rfl).inv) (zero_add (0 : ℤ)) 1
        (by norm_num) (by simp [I.cochainComplex_d 0 1 0 1 rfl rfl,
          reassoc_of% I.ι_f_zero_comp_complex_d])) = ShiftedHom.mk₀ 0 rfl I.ι' := by
  apply HomologicalComplex.hom_ext
  intro p
  by_cases hp : p = 0
  · subst p
    simp [CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply,
      ShiftedHom.mk₀, I.ι'_f_zero, CategoryTheory.shiftFunctorZero',
      CochainComplex.shiftFunctorZero_inv_app_f,
      CochainComplex.HomComplex.Cochain.rightShift_v (n := 0) _ 0 0 (by simp) 0 0 (by simp) 0
        (by simp)]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _

private theorem augmentation_extMk {C : Type*} [Category C] [Abelian C] [HasExt C]
    {A : C} (I : InjectiveResolution A) :
    I.extMk (I.ι.f 0) 1 rfl I.ι_f_zero_comp_complex_d = Abelian.Ext.mk₀ (𝟙 A) := by
  let := HasDerivedCategory.standard C
  ext
  rw [I.extMk_hom, Abelian.Ext.mk₀_hom]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, ShiftedHom.mk₀_id_comp]
  erw [augmentation_cocycle I, ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp_mk₀]
  simp

/-- The augmented section one corresponds to the scalar-unit morphism in degree-zero Ext. -/
private theorem scalar_unit_class_ext {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) :
    scalarCohomologyExtEquiv f (SheafOfModules.unit X.ringCatSheaf) 0
      (scalarUnitCohomologyClass f) = Abelian.Ext.mk₀ (scalarUnitMorphism f) := by
  classical
  let : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
    hasExt_of_enoughInjectives.{u, u, u + 1} _
  let U := SheafOfModules.unit X.ringCatSheaf
  let I := injectiveResolution U
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let z := (I.toRightDerivedZero' S).hom (1 : Γ(X, ⊤))
  have hz : (I.ι.f 0).val.app (op ⊤) (1 : Γ(X, ⊤)) =
      (RingedSpace.globalSectionsComplex I).iCycles 0 z := by
    exact (ConcreteCategory.congr_hom (I.toRightDerivedZero'_comp_iCycles S)
      (1 : Γ(X, ⊤))).symm
  have he := Classical.choose_spec (exists_moduleExtEquiv U 0) I z (I.ι.f 0)
    I.ι_f_zero_comp_complex_d hz
  have hc : scalarUnitCohomologyClass f =
      (I.isoRightDerivedObj S 0).inv
        ((RingedSpace.globalSectionsComplex I).homologyπ 0 z) := by
    unfold scalarUnitCohomologyClass
    rw [I.toRightDerivedZero_eq S]
    rfl
  have hm : moduleExtEquiv U 0 (scalarUnitCohomologyClass f) =
      I.extMk (I.ι.f 0) 1 rfl I.ι_f_zero_comp_complex_d := by
    rw [hc]
    simpa only [moduleExtEquiv, S] using he
  unfold scalarCohomologyExtEquiv scalarCohomologyExtMap scalarExtMap
  change (Abelian.Ext.mk₀ (scalarUnitMorphism f)).comp
    ((moduleExtEquiv U 0 (scalarUnitCohomologyClass f)).mapExactFunctor
      (scalarFunctor f)) (zero_add 0) = _
  rw [hm]
  rw [augmentation_extMk, Abelian.Ext.mapExactFunctor_mk₀, CategoryTheory.Functor.map_id,
    Abelian.Ext.mk₀_comp_mk₀]
  erw [Category.comp_id]


private theorem homEquiv_unique {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G)
    (c : C) (d : D) (v : F'.obj c ⟶ d) :
    a.homEquiv c d ((a.leftAdjointUniq b).hom.app c ≫ v) = b.homEquiv c d v := by
  rw [a.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    b.homEquiv_unit]

-- Adjunction comparisons require unfolding several sheaf evaluation functors.
/-- The scalar-unit coefficient morphism commutes with inverse image and the
structure-sheaf coefficient map. -/
private theorem scalar_unit_morphism_pullback {k : Type u} [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (t : Y ⟶ X) (h : t ≫ f = g) :
    (scalarInverseUnitIso (k := k) t).inv ≫
        (scalarInverseImage t).map (scalarUnitMorphism f) ≫
        scalarPullbackCoefficient f g t h (SheafOfModules.unit X.ringCatSheaf) ≫
        scalarHom g (tensorPullbackObjUnitToUnit t) = scalarUnitMorphism g := by
  classical
  let cX := constantSheafAdj (Opens.grothendieckTopology X)
    (ModuleCat.{u} k) isTerminalTop
  let cY := constantSheafAdj (Opens.grothendieckTopology Y)
    (ModuleCat.{u} k) isTerminalTop
  let a := (Opens.map t.base).sheafAdjunctionContinuous
    (ModuleCat.{u} k) (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y)
  let e := ((Opens.map t.base).constantSheafsheafPullbackIso
    (ModuleCat.{u} k) (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y) isTerminalTop isTerminalTop).app (ModuleCat.of k k)
  rw [← cancel_epi (constantScalarUnitIso (X := Y) (k := k)).hom]
  unfold scalarInverseUnitIso scalarUnitMorphism
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc,
    Iso.hom_inv_id_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  change e.inv ≫ (scalarInverseImage t).map
      ((cX.homEquiv _ (scalarSheaf f (SheafOfModules.unit X.ringCatSheaf))).symm
        (scalarUnitLinear f)) ≫
      scalarPullbackCoefficient f g t h (SheafOfModules.unit X.ringCatSheaf) ≫
      scalarHom g (tensorPullbackObjUnitToUnit t) =
        (cY.homEquiv _ (scalarSheaf g (SheafOfModules.unit Y.ringCatSheaf))).symm
          (scalarUnitLinear g)
  rw [← cancel_epi e.hom, Iso.hom_inv_id_assoc]
  let b := (cX.comp a).ofNatIsoRight
    ((Opens.map t.base).sheafPushforwardContinuousCompSheafSectionsObjIso
      (ModuleCat.{u} k) (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) (Opposite.op ⊤))
  apply (b.homEquiv _ _).injective
  have he : b.homEquiv _ _ (e.hom ≫
      (cY.homEquiv _ (scalarSheaf g (SheafOfModules.unit Y.ringCatSheaf))).symm
        (scalarUnitLinear g)) = scalarUnitLinear g := by
    exact (homEquiv_unique b cY _ _ _).trans
      ((cY.homEquiv _ (scalarSheaf g (SheafOfModules.unit Y.ringCatSheaf))).apply_symm_apply
        (scalarUnitLinear g))
  rw [he]
  change cX.homEquiv _ _ (a.homEquiv _ _
    ((scalarInverseImage t).map
      ((cX.homEquiv _ _).symm (scalarUnitLinear f)) ≫
      scalarPullbackCoefficient f g t h (SheafOfModules.unit X.ringCatSheaf) ≫
      scalarHom g (tensorPullbackObjUnitToUnit t))) = scalarUnitLinear g
  erw [a.homEquiv_naturality_left, cX.homEquiv_naturality_right,
    Equiv.apply_symm_apply, a.homEquiv_naturality_right]
  ext
  change (tensorPullbackObjUnitToUnit t).val.app
      (Opposite.op ((Opens.map t.base).obj ⊤))
      ((a.homEquiv _ _
        (scalarPullbackCoefficient f g t h (SheafOfModules.unit X.ringCatSheaf))).hom.app
        (Opposite.op ⊤) (scalarMap f ⊤ 1)) = scalarMap g ⊤ 1
  rw [(scalarMap f ⊤).map_one, (scalarMap g ⊤).map_one]
  rw [show (a.homEquiv _ _
      (scalarPullbackCoefficient f g t h (SheafOfModules.unit X.ringCatSheaf))).hom.app
      (Opposite.op ⊤) (1 : Γ(X, ⊤)) =
      ((Classical.choose (exists_tensorPullbackAdjunction t)).unit.app
        (SheafOfModules.unit X.ringCatSheaf)).val.app (Opposite.op ⊤) (1 : Γ(X, ⊤)) from by
    simpa only [scalarPullbackCoefficient, a] using
      Classical.choose_spec
        (exists_scalarPullbackCoefficient f g t h (SheafOfModules.unit X.ringCatSheaf))
        ⊤ (1 : Γ(X, ⊤))]
  have hu := congrArg
    (fun v : SheafOfModules.unit X.ringCatSheaf ⟶
      (pushforward t).obj (SheafOfModules.unit Y.ringCatSheaf) ↦
        v.val.app (Opposite.op ⊤) (1 : Γ(X, ⊤)))
    (tensorPullbackObjUnitToUnit_isIso t).2
  change (tensorPullbackObjUnitToUnit t).val.app
      (Opposite.op ((Opens.map t.base).obj ⊤))
      (((Classical.choose (exists_tensorPullbackAdjunction t)).unit.app
        (SheafOfModules.unit X.ringCatSheaf)).val.app (Opposite.op ⊤) (1 : Γ(X, ⊤))) =
        (t.toRingCatSheafHom.hom.app (Opposite.op ⊤)).hom (1 : Γ(X, ⊤)) at hu
  rw [(t.toRingCatSheafHom.hom.app (Opposite.op ⊤)).hom.map_one] at hu
  exact hu


end

/-- Pullback followed by the structure-sheaf coefficient map preserves the class of one. -/
theorem scalar_unit_class_pullback (k : Type u) [Field k]
    (X Y : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (t : Y ⟶ X) (h : t ≫ f = g) :
    scalarCohomologyMap g (tensorPullbackObjUnitToUnit t) 0
      (scalarCohomologyPullback f g t h (SheafOfModules.unit X.ringCatSheaf) 0
        (scalarUnitCohomologyClass f)) = scalarUnitCohomologyClass g := by
  let : MonoidalCategory (KSheaf X k) := Sheaf.monoidalCategory _ _
  let : MonoidalCategory (KSheaf Y k) := Sheaf.monoidalCategory _ _
  let : HasExt.{u + 1} (KSheaf X k) := HasExt.standard _
  let : HasExt.{u + 1} (KSheaf Y k) := HasExt.standard _
  apply (scalarCohomologyExtEquiv g _ 0).injective
  rw [scalarCohomologyExtEquiv_map]
  unfold scalarCohomologyPullback
  rw [AddEquiv.apply_symm_apply, scalar_unit_class_ext, scalar_unit_class_ext]
  simp only [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
  rw [Category.assoc, Category.assoc, scalar_unit_morphism_pullback]

end AlgebraicGeometry.Scheme.Modules
