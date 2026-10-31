/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletedTensorCommonLiftTensorUnit
import WeilConjectures.CategoryTheory.TensorUnitComparisonUnique

/-! # Normalizing the unit comparison at the common coefficient unit

Source: BS Remark 6.8.15; cancellation and full faithfulness of tensoring with a unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization

/-- For a fixed common-stage tensorator, there is exactly one unit comparison
satisfying the right-unit equation at the common coefficient unit itself.
This does not assert the equation at other objects or any other monoidal constraint.

Source: BS Remark 6.8.15; elementary normalization of a unit comparison.
(blueprint: lem-sf-adic-completed-tensor-common-lift-unit-normalization).

Proof: write U for the common coefficient unit and V for its ordinary realization.
The given unit comparison identifies V with the native tensor unit, so tensoring
on the left by V is fully faithful: transport full faithfulness along that
comparison and the natural left unitor. Write q for the tensorator at (U,U)
followed by the realized common right unitor. Lift the isomorphism rho_V followed
by q inverse along V tensor -. Its preimage is the required unit comparison.
The defining preimage equation proves the right-unit equation. Cancellation of q
and faithfulness of V tensor - prove uniqueness. No assertion about arbitrary
unit choices, finite models, nonzero objects, or residue characteristic is used. -/
theorem completed_tensor_common_lift_unit_normalization
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)]
    (closed : CoefficientClosedStructure (ambientHom l X R))
    (models : CoefficientTensorModels.{u + 1, u + 1, u}
      (ProEt.topology X) (ring l X R) closed)
    (symmetry : @SymmetricCategory _ _ closed.monoidal)
    (data : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry) :
    ∃! unit : closed.monoidal.tensorUnit ≅
        (ordinary l X R).obj (pullbackTensorCommonUnit l (PadicAlgCl l) X),
      closed.tensor.map (Prod.mkHom (𝟙 _) unit.hom) ≫
          data.tensor.hom.app
            (pullbackTensorCommonUnit l (PadicAlgCl l) X,
             pullbackTensorCommonUnit l (PadicAlgCl l) X) ≫
          (ordinary l X R).map (pullbackTensorCommonRightUnitor l (PadicAlgCl l) X
            (pullbackTensorCommonUnit l (PadicAlgCl l) X)).hom =
        (closed.monoidal.rightUnitor ((ordinary l X R).obj
          (pullbackTensorCommonUnit l (PadicAlgCl l) X))).hom := by
  let := closed.monoidal
  let D := DerivedCategory (modules l X R)
  let U := pullbackTensorCommonUnit l (PadicAlgCl l) X
  let V := (ordinary l X R).obj U
  let q := data.tensor.app (U, U) ≪≫
    (ordinary l X R).mapIso (pullbackTensorCommonRightUnitor l (PadicAlgCl l) X U)
  have : (MonoidalCategory.tensorUnitLeft D).Full :=
    Functor.Full.of_iso (MonoidalCategory.leftUnitorNatIso D).symm
  have : (MonoidalCategory.tensorUnitLeft D).Faithful :=
    Functor.Faithful.of_iso (MonoidalCategory.leftUnitorNatIso D).symm
  let t : MonoidalCategory.tensorUnitLeft D ≅ MonoidalCategory.tensorLeft V :=
    NatIso.ofComponents
      (fun B ↦ MonoidalCategory.whiskerRightIso data.unit B)
      (fun f ↦ MonoidalCategory.whisker_exchange data.unit.hom f)
  have : (MonoidalCategory.tensorLeft V).Full := Functor.Full.of_iso t
  have : (MonoidalCategory.tensorLeft V).Faithful := Functor.Faithful.of_iso t
  let a := (MonoidalCategory.tensorLeft V).preimageIso
    (closed.monoidal.rightUnitor V ≪≫ q.symm)
  have ha : closed.tensor.map (Prod.mkHom (𝟙 V) a.hom) ≫ q.hom =
      (closed.monoidal.rightUnitor V).hom := by
    dsimp only [CoefficientClosedStructure.tensor]
    rw [MonoidalCategory.tensor_map, MonoidalCategory.id_tensorHom]
    change (MonoidalCategory.tensorLeft V).map a.hom ≫ q.hom = _
    simp only [a, Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_hom,
      Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply Iso.ext
  exact tensorUnitComparison_unique data.unit q b.hom a.hom (hb.trans ha.symm)

end WeilConjectures.AdicQbarRealization
