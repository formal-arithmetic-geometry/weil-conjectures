/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
import all Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful

/-!
# Canonical local scalar adjoints at every finite coefficient stage

Source: archived ModuleObject/Colimit/TwoColimit.lean, (Obj) overlap descent paragraph.
(blueprint: def-weil-pbc-condensed-local-coefficient-adjoints).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
private lemma mono_pulled_coefficient_unit
    (T X Y : Scheme.{u}) (f : X ⟶ T) (g : Y ⟶ X)
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      ((upperStar Ab.{u + 1} g).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))) :
    Mono ((Mod.extendRestrictAdjunction ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).unit.app P) := by
  let H := upperStarFromPoint T
  let K := upperStar Ab.{u + 1} f
  let J := upperStar Ab.{u + 1} g
  let r := J.map (K.map (H.map (Profinite.condensedProjection ℓ E)))
  have hlin := CategoryTheory.mapLinear J _ _
    (CategoryTheory.mapLinear K _ _
      (CategoryTheory.mapLinear H _ _ (Profinite.condensedProjection_linear ℓ E)))
  have hret : J.map (K.map (padicSubfieldRingObjToPadicAlgCl T ℓ E)) ≫ r = 𝟙 _ := by
    change J.map (K.map (H.map _)) ≫ J.map (K.map (H.map _)) = 𝟙 _
    rw [← J.map_comp, ← K.map_comp, ← H.map_comp,
      Profinite.condensedProjection_retract, H.map_id, K.map_id, J.map_id]
  have hs := unit_retract _ _ _ r hlin hret
  have hsP : (Mod.extendRestrictAdjunction (J.map (K.map
      (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).unit.app P ≫
        (retractNat _ _ _ r hlin).app P = 𝟙 P := congr_app hs P
  exact ⟨fun a b h ↦ by
    have h' := congrArg (· ≫ (retractNat _ _ _ r hlin).app P) h
    simp only [Category.assoc] at h'
    change a ≫ ((Mod.extendRestrictAdjunction (J.map (K.map
        (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).unit.app P ≫
        (retractNat _ _ _ r hlin).app P) =
      b ≫ ((Mod.extendRestrictAdjunction (J.map (K.map
        (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).unit.app P ≫
        (retractNat _ _ _ r hlin).app P) at h'
    rw [hsP] at h'
    change a ≫ 𝟙 P = b ≫ 𝟙 P at h'
    exact (Category.comp_id a).symm.trans (h'.trans (Category.comp_id b))⟩


section LocalAdjoints

variable (T X : Scheme.{u}) (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
  (Y : Scheme.{u}) (g : Y ⟶ X)
  (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    ((upperStar Ab.{u + 1} g).obj
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))

/-- The specified finite scalar extension of a local module. -/
noncomputable def finiteCoefficientLocalModel
    (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F) :=
  (Mod.extendScalars ((upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)))).obj P

variable
  (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
  (a : (Mod.extendScalars ((upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj P ⟶
      ((upperStar Ab.{u + 1} g).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M)
  (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F)

/-- Tensor transitivity followed by the supplied map to the local algebraic-closure module. -/
noncomputable def finiteCoefficientLocalTensorMap :
    (Mod.extendScalars ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ F)))).obj
        (finiteCoefficientLocalModel T X f ℓ E Y g P F hEF) ⟶
      ((upperStar Ab.{u + 1} g).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M :=
  ((Mod.extendScalarsComp _ _).symm.app P).hom ≫
    ((Mod.extendScalarsIsoOfEq (by
      rw [← Functor.map_comp, ← Functor.map_comp,
        padicSubfieldRingObjMap_comp_toPadicAlgCl])).app P).hom ≫ a

/-- The canonical adjoint into the restriction of the given module, at stage `F`. -/
noncomputable def finiteCoefficientLocalAdjoint :
    finiteCoefficientLocalModel T X f ℓ E Y g P F hEF ⟶
      ((upperStar Ab.{u + 1} g).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))).obj
          ((Mod.comap ((upperStar Ab.{u + 1} f).map
            (padicSubfieldRingObjToPadicAlgCl T ℓ F))).obj M) :=
  (Mod.extendRestrictAdjunction ((upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map
      (padicSubfieldRingObjToPadicAlgCl T ℓ F)))).homEquiv _ _
        (finiteCoefficientLocalTensorMap T X f ℓ E Y g P M a F hEF) ≫
    ((upperStar Ab.{u + 1} g).mapModComapIso ((upperStar Ab.{u + 1} f).map
      (padicSubfieldRingObjToPadicAlgCl T ℓ F))).inv.app M

/-- An invertible original model map remains invertible after tensor transitivity. -/
theorem isIso_finiteCoefficientLocalTensorMap [IsIso a] :
    IsIso (finiteCoefficientLocalTensorMap T X f ℓ E Y g P M a F hEF) := by
  unfold finiteCoefficientLocalTensorMap
  infer_instance

/-- A local isomorphism has monic scalar adjoints at every finite stage.
The coefficient-linear projection splits the unit, also after both inverse images. -/
theorem mono_finiteCoefficientLocalAdjoint [IsIso a] :
    Mono (finiteCoefficientLocalAdjoint T X f ℓ E Y g P M a F hEF) := by
  have := mono_pulled_coefficient_unit T X Y f g ℓ F
    (finiteCoefficientLocalModel T X f ℓ E Y g P F hEF)
  have := isIso_finiteCoefficientLocalTensorMap T X f ℓ E Y g P M a F hEF
  unfold finiteCoefficientLocalAdjoint
  rw [Adjunction.homEquiv_unit]
  infer_instance

/-- Taking the scalar adjunct of the canonical local map recovers its tensor map. -/
theorem finiteCoefficientLocalAdjoint_scalarAdjoint :
    ((Mod.extendRestrictAdjunction ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map
        (padicSubfieldRingObjToPadicAlgCl T ℓ F)))).homEquiv
          (finiteCoefficientLocalModel T X f ℓ E Y g P F hEF)
          (((upperStar Ab.{u + 1} g).mapMod
            ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M)).symm
              (finiteCoefficientLocalAdjoint T X f ℓ E Y g P M a F hEF ≫
                ((upperStar Ab.{u + 1} g).mapModComapIso ((upperStar Ab.{u + 1} f).map
                  (padicSubfieldRingObjToPadicAlgCl T ℓ F))).hom.app M) =
      finiteCoefficientLocalTensorMap T X f ℓ E Y g P M a F hEF := by
  unfold finiteCoefficientLocalAdjoint
  rw [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id, Equiv.symm_apply_apply]

end LocalAdjoints
end AlgebraicGeometry.ProEtale
