/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange

/-! # The ordinary pullback compositor on unit generators

The compositor of ordinary completed module pullback is the adjunction conjugate of the
fiber-product pasting of direct images, so it sends an iterated unit generator to the restriction
of the unit generator of the composite.

## References

* Stacks Tag 03D8
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

variable {V W T : Scheme.{u}} (h : T ⟶ W) (k : W ⟶ V)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The inverse of the ordinary pullback compositor sends an iterated unit generator to the
restriction of the unit generator of the composite. -/
theorem pbcActualModulePullCompIso_inv_app_unit (M : pbcModules V (pbcAdicCompletion V d))
    (U : V.ProEt) (x : M.val.obj (op U)) :
    ((pbcActualModulePullCompIso h k d).inv.app M).val.app
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange k).obj U)))
      (pbcActualModuleUnitSection h d ((pbcActualModulePull k d).obj M)
        ((proEtaleBaseChange k).obj U) (pbcActualModuleUnitSection k d M U x)) =
    ((pbcActualModulePull (h ≫ k) d).obj M).val.map
      ((MorphismProperty.Over.pullbackComp h k).inv.app U).op
      (pbcActualModuleUnitSection (h ≫ k) d M U x) := by
  have hunit {S T : Scheme.{u}} (f : S ⟶ T) (N : pbcModules T (pbcAdicCompletion T d))
      (U : T.ProEt) (y : N.val.obj (op U)) :
      ((pbcActualModuleAdjunction f d).unit.app N).val.app (op U) y =
        pbcActualModuleUnitSection f d N U y :=
    (pbcActualModuleAdjunction_exists f d).exists.choose_spec N U y
  have hdirect (N : pbcModules T (pbcAdicCompletion T d)) (U : V.ProEt)
      (y : ((pbcActualModulePush h d ⋙ pbcActualModulePush k d).obj N).val.obj (op U)) :
      ((pbcActualModuleDirectCompIso h k d).hom.app N).val.app (op U) y =
        N.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app U).op y :=
    (pbcActualModuleDirectCompIso_exists h k d).exists.choose_spec N U y
  have key := congrArg (fun f ↦ f.val.app (op U) x)
    (unit_conjugateEquiv_symm (pbcActualModuleAdjunction (h ≫ k) d)
      ((pbcActualModuleAdjunction k d).comp (pbcActualModuleAdjunction h d))
      (pbcActualModuleDirectCompIso h k d).inv M)
  simp only [Adjunction.comp_unit_app] at key
  change ((pbcActualModuleDirectCompIso h k d).inv.app _).val.app (op U)
      (((pbcActualModuleAdjunction (h ≫ k) d).unit.app M).val.app (op U) x) =
    ((pbcActualModulePullCompIso h k d).inv.app M).val.app
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange k).obj U)))
      (((pbcActualModuleAdjunction h d).unit.app ((pbcActualModulePull k d).obj M)).val.app
        (op ((proEtaleBaseChange k).obj U))
        (((pbcActualModuleAdjunction k d).unit.app M).val.app (op U) x)) at key
  simp only [hunit] at key
  rw [← key]
  set N := (pbcActualModulePull (h ≫ k) d).obj M
  set y := pbcActualModuleUnitSection (h ≫ k) d M U x
  have h1 : y = N.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app U).op
      (((pbcActualModuleDirectCompIso h k d).inv.app N).val.app (op U) y) := by
    have h2 := hdirect N U (((pbcActualModuleDirectCompIso h k d).inv.app N).val.app (op U) y)
    rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val,
      Iso.inv_hom_id_app] at h2
    exact h2
  conv_rhs => rw [h1]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, Iso.inv_hom_id_app, op_id]
  simp
  rfl

end AlgebraicGeometry.Scheme

