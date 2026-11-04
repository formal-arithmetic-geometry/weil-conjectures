/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.ScalarDirectImage.PbcActualPullProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalAdjunctionUnit
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-! # The ordinary scalar/pullback comparison under the scalar units

Ordinary module-level input for the derived statement
`pbcActualScalarDerivedPullIso_restriction_unit`.

Source: Stacks Tags 03D2, 03EL and 03EK
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)

/-- Transporting a section along an object equality and back is the identity. -/
theorem sheafOfModules_eqToHom_val_app_symm {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat} {M N : SheafOfModules R} (h : M = N)
    (U : Cᵒᵖ) (z : N.val.obj U) :
    (eqToHom h).val.app U ((eqToHom h.symm).val.app U z) = z := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual module adjunction unit, followed by the object equality with the canonical
pullback, is the canonical module adjunction unit.
Source: Stacks Tags 03D2 and 03EK
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
theorem pbcActualModuleAdjunction_unit_pullIso (M : pbcModules Y (pbcAdicCompletion Y d)) :
    (pbcActualModuleAdjunction g d).unit.app M ≫
        (pbcActualModulePush g d).map ((pbcActualModulePullIso g d).hom.app M) =
      (proEtaleRingModuleAdjunction g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (pbcActualCoefficientIso g d)).unit.app M := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  have h1 := (pbcActualModuleAdjunction_exists g d).exists.choose_spec M U.unop x
  have h2 := proEtaleRingModuleAdjunction_normalized g _ _ (pbcActualCoefficientIso g d) M
    U.unop x
  rw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  erw [h1]
  have h3 := sheafOfModules_eqToHom_val_app_symm
    ((completedAdicChangeData X (completedCoefficientMap g d)).choose_spec.choose
      ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).obj M))
    (op ((proEtaleBaseChange g).obj U.unop))
    (proEtaleRingModuleUnitSection g _ _ (pbcActualCoefficientIso g d) M U.unop x)
  exact h3.trans h2.symm


/-- The inverse object equality, after the canonical module adjunction unit, is the actual
module adjunction unit.
Source: Stacks Tags 03D2 and 03EK
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
theorem pbcActualModuleAdjunction_unit_eq (M : pbcModules Y (pbcAdicCompletion Y d)) :
    (proEtaleRingModuleAdjunction g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (pbcActualCoefficientIso g d)).unit.app M ≫
        (pbcActualModulePush g d).map ((pbcActualModulePullIso g d).inv.app M) =
      (pbcActualModuleAdjunction g d).unit.app M := by
  rw [← pbcActualModuleAdjunction_unit_pullIso, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

variable {B : Type (u + 1)} [CommRing B] (dA : AdicCoefficientDatum A)
    (dB : AdicCoefficientDatum B)
    (φY : pbcAdicCompletion Y dA ⟶ pbcAdicCompletion Y dB)
    (φX : pbcAdicCompletion X dA ⟶ pbcAdicCompletion X dB)
    (hφ : pbcActualCoefficientRingMap Y φY ≫ pbcActualStructureMap g dB =
      pbcActualStructureMap g dA ≫
        (proEtaleSheafDirectImage g RingCat.{u + 1}).map (pbcActualCoefficientRingMap X φX))
    (hc : (pbcActualCoefficientIso g dA).hom ≫ φX =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map φY ≫
        (pbcActualCoefficientIso g dB).hom)

/-- The two identity-on-sections restriction/direct-image comparisons agree.
Source: Stacks Tag 03EL
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
theorem pbcActualScalarRightIso_hom_eq :
    (pbcActualScalarRightIso g dA dB φY φX hφ).hom =
      (proEtaleRingRestrictionDirectImage g (pbcAdicCompletion Y dA) (pbcAdicCompletion Y dB)
        (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
        (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc).hom := by
  ext N U x
  exact ((pbcActualScalarRightIso_exists g dA dB φY φX hφ).exists.choose_spec N U x).trans
    ((Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique g
      (pbcAdicCompletion Y dA) (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA)
      (pbcAdicCompletion X dB) φY φX (pbcActualCoefficientIso g dA)
      (pbcActualCoefficientIso g dB) hc)).1 N U x).symm


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordinary scalar/pullback comparison, transposed along the scalar units, is the
canonical restriction/pullback comparison.
Source: Stacks Tags 03D2, 03EL and 03EK
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: transpose along the actual module adjunction. The scalar/pullback comparison is
the conjugate of the identity-on-sections restriction/direct-image comparison, while the
canonical comparison is its mate under the canonical module adjunctions. The two module
adjunctions differ by the object equality of pullbacks. -/
theorem pbcActualScalarOrdinaryPullIso_restriction_unit
    (M : pbcModules Y (pbcAdicCompletion Y dA)) :
    (pbcScalarAdjunction φX).unit.app ((pbcActualModulePull g dA).obj M) ≫
        (pbcRestrict φX).map ((pbcActualScalarOrdinaryPullIso g dA dB φY φX hφ).inv.app M) =
      (pbcActualModulePull g dA).map ((pbcScalarAdjunction φY).unit.app M) ≫
        (pbcActualModulePullIso g dA).hom.app _ ≫
        (proEtaleRingRestrictionPullbackInv g (pbcAdicCompletion Y dA)
          (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
          (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc).app
            ((pbcExtend φY).obj M) ≫
        (pbcRestrict φX).map ((pbcActualModulePullIso g dB).inv.app _) := by
  apply ((pbcActualModuleAdjunction g dA).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  have hconj := unit_conjugateEquiv_symm
    ((pbcScalarAdjunction φY).comp (pbcActualModuleAdjunction g dB))
    ((pbcActualModuleAdjunction g dA).comp (pbcScalarAdjunction φX))
    (pbcActualScalarRightIso g dA dB φY φX hφ).hom M
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at hconj
  have hmate :
      (proEtaleRingRestrictScalars φY).map
        ((proEtaleRingModuleAdjunction g (pbcAdicCompletion Y dB) (pbcAdicCompletion X dB)
          (pbcActualCoefficientIso g dB)).unit.app ((pbcExtend φY).obj M)) ≫
        (proEtaleRingRestrictionDirectImage g (pbcAdicCompletion Y dA) (pbcAdicCompletion Y dB)
          (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
          (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc).hom.app _ =
      (proEtaleRingModuleAdjunction g (pbcAdicCompletion Y dA) (pbcAdicCompletion X dA)
          (pbcActualCoefficientIso g dA)).unit.app _ ≫
        (proEtaleRingModuleDirectImage g (pbcAdicCompletion Y dA) (pbcAdicCompletion X dA)
          (pbcActualCoefficientIso g dA)).map
          ((proEtaleRingRestrictionPullbackInv g (pbcAdicCompletion Y dA)
            (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
            (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc).app
              ((pbcExtend φY).obj M)) := by
    rw [← restrictionPullback_mate]
    exact unit_mateEquiv _ _ _ _
  have hconj' :
      (pbcActualModuleAdjunction g dA).unit.app M ≫
        (pbcActualModulePush g dA).map
          ((pbcScalarAdjunction φX).unit.app ((pbcActualModulePull g dA).obj M) ≫
            (pbcRestrict φX).map ((pbcActualScalarOrdinaryPullIso g dA dB φY φX hφ).inv.app M)) =
      (pbcScalarAdjunction φY).unit.app M ≫
        (pbcRestrict φY).map ((pbcActualModuleAdjunction g dB).unit.app ((pbcExtend φY).obj M)) ≫
        (pbcActualScalarRightIso g dA dB φY φX hφ).hom.app
          ((pbcActualModulePull g dB).obj ((pbcExtend φY).obj M)) := by
    rw [Functor.map_comp, ← Category.assoc]
    exact hconj.symm
  have hnat := (pbcActualModuleAdjunction g dA).unit.naturality
    ((pbcScalarAdjunction φY).unit.app M)
  have hA := pbcActualModuleAdjunction_unit_pullIso g dA
    ((pbcRestrict φY).obj ((pbcExtend φY).obj M))
  have hB := pbcActualModuleAdjunction_unit_eq g dB ((pbcExtend φY).obj M)
  have hd := (proEtaleRingRestrictionDirectImage g (pbcAdicCompletion Y dA)
    (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
    (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc).hom.naturality
      ((pbcActualModulePullIso g dB).inv.app ((pbcExtend φY).obj M))
  rw [hconj', pbcActualScalarRightIso_hom_eq g dA dB φY φX hφ hc]
  have hnat' : (pbcActualModuleAdjunction g dA).unit.app M ≫
      (pbcActualModulePush g dA).map
        ((pbcActualModulePull g dA).map ((pbcScalarAdjunction φY).unit.app M)) =
      (pbcScalarAdjunction φY).unit.app M ≫
        (pbcActualModuleAdjunction g dA).unit.app
          ((pbcRestrict φY).obj ((pbcExtend φY).obj M)) := hnat.symm
  have hd' :
      (proEtaleRingRestrictionDirectImage g (pbcAdicCompletion Y dA)
        (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
        (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc).hom.app
          ((proEtaleRingModulePullback g (pbcAdicCompletion Y dB) (pbcAdicCompletion X dB)
            (pbcActualCoefficientIso g dB)).obj ((pbcExtend φY).obj M)) ≫
        (pbcActualModulePush g dA).map
          ((pbcRestrict φX).map ((pbcActualModulePullIso g dB).inv.app ((pbcExtend φY).obj M))) =
      (pbcRestrict φY).map ((pbcActualModulePush g dB).map
          ((pbcActualModulePullIso g dB).inv.app ((pbcExtend φY).obj M))) ≫
        (proEtaleRingRestrictionDirectImage g (pbcAdicCompletion Y dA)
        (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
        (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc).hom.app
          ((pbcActualModulePull g dB).obj ((pbcExtend φY).obj M)) := hd.symm
  calc _ = (pbcScalarAdjunction φY).unit.app M ≫
        (pbcRestrict φY).map
          ((proEtaleRingModuleAdjunction g (pbcAdicCompletion Y dB) (pbcAdicCompletion X dB)
            (pbcActualCoefficientIso g dB)).unit.app ((pbcExtend φY).obj M) ≫
          (pbcActualModulePush g dB).map
            ((pbcActualModulePullIso g dB).inv.app ((pbcExtend φY).obj M))) ≫
        (proEtaleRingRestrictionDirectImage g (pbcAdicCompletion Y dA)
          (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
          (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc).hom.app
            ((pbcActualModulePull g dB).obj ((pbcExtend φY).obj M)) := by
        rw [hB]
    _ = (pbcScalarAdjunction φY).unit.app M ≫
        (pbcRestrict φY).map
          ((proEtaleRingModuleAdjunction g (pbcAdicCompletion Y dB) (pbcAdicCompletion X dB)
            (pbcActualCoefficientIso g dB)).unit.app ((pbcExtend φY).obj M)) ≫
        (proEtaleRingRestrictionDirectImage g (pbcAdicCompletion Y dA)
          (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
          (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc).hom.app _ ≫
        (pbcActualModulePush g dA).map
          ((pbcRestrict φX).map
            ((pbcActualModulePullIso g dB).inv.app ((pbcExtend φY).obj M))) := by
        rw [hd', Functor.map_comp, Category.assoc]
    _ = (pbcScalarAdjunction φY).unit.app M ≫
        (proEtaleRingModuleAdjunction g (pbcAdicCompletion Y dA) (pbcAdicCompletion X dA)
          (pbcActualCoefficientIso g dA)).unit.app _ ≫
        (pbcActualModulePush g dA).map
          ((proEtaleRingRestrictionPullbackInv g (pbcAdicCompletion Y dA)
            (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
            (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc).app
              ((pbcExtend φY).obj M)) ≫
        (pbcActualModulePush g dA).map
          ((pbcRestrict φX).map
            ((pbcActualModulePullIso g dB).inv.app ((pbcExtend φY).obj M))) := by
        rw [← Category.assoc ((pbcRestrict φY).map _), hmate, Category.assoc]
        rfl
    _ = _ := by
        rw [← hA, Functor.map_comp, Functor.map_comp, Functor.map_comp, reassoc_of% hnat']
        simp only [Category.assoc]
        rfl

end AlgebraicGeometry.Scheme
