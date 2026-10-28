/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicCompletedTensorCommonLiftTensorUnit
import Sheaf.Paper.AdicCompletedTensorCommonLiftUnitNormalization
import Sheaf.Paper.AdicCompletedTensorCommonLiftConstraintsLeftUnit
import Sheaf.Paper.AdicCompletedTensorCommonLiftConstraintsAssociative
import Sheaf.Paper.CommonStageTensorTriangle

/-! Right-unit equation for the common-stage completed tensor lift.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: new-sf-adic-completed-tensor-common-lift-constraints-right-unit).
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization

open MonoidalCategory in
private theorem right_unit_of_left_associativity
    {C D : Type*} [Category C] [Category D] [MonoidalCategory D]
    (F : C ⥤ D) (T : C × C ⥤ C) (U : C)
    (a : ∀ A, T.obj (T.obj (A, U), U) ≅ T.obj (A, T.obj (U, U)))
    (l : T.obj (U, U) ≅ U) (r : ∀ A, T.obj (A, U) ≅ A)
    (μ : F.prod F ⋙ tensor D ≅ T ⋙ F) (e : 𝟙_ D ≅ F.obj U)
    (ht : ∀ A, (a A).hom ≫ T.map (Prod.mkHom (𝟙 A) l.hom) =
      T.map (Prod.mkHom (r A).hom (𝟙 U)))
    (ha : ∀ A,
      (tensor D).map (Prod.mkHom (μ.hom.app (A, U)) (𝟙 _)) ≫
          μ.hom.app (T.obj (A, U), U) ≫ F.map (a A).hom =
        (α_ (F.obj A) (F.obj U) (F.obj U)).hom ≫
          (tensor D).map (Prod.mkHom (𝟙 _) (μ.hom.app (U, U))) ≫
          μ.hom.app (A, T.obj (U, U)))
    (hl : (tensor D).map (Prod.mkHom e.hom (𝟙 _)) ≫ μ.hom.app (U, U) ≫
      F.map l.hom = (λ_ (F.obj U)).hom) (A : C) :
    (tensor D).map (Prod.mkHom (𝟙 _) e.hom) ≫ μ.hom.app (A, U) ≫
      F.map (r A).hom = (ρ_ (F.obj A)).hom := by
  have : (tensorUnitRight D).Faithful :=
    Functor.Faithful.of_iso (rightUnitorNatIso D).symm
  let t : tensorUnitRight D ≅ tensorRight (F.obj U) :=
    NatIso.ofComponents (fun B ↦ whiskerLeftIso B e)
      (fun f ↦ (whisker_exchange f e.hom).symm)
  have : (tensorRight (F.obj U)).Faithful := Functor.Faithful.of_iso t
  apply (tensorRight (F.obj U)).map_injective
  apply (cancel_mono (μ.hom.app (A, U))).1
  have hn := μ.hom.naturality (Prod.mkHom (r A).hom (𝟙 U))
  change (tensor D).map (Prod.mkHom (F.map (r A).hom) (F.map (𝟙 U))) ≫
    μ.hom.app (A, U) = μ.hom.app (T.obj (A, U), U) ≫
      F.map (T.map (Prod.mkHom (r A).hom (𝟙 U))) at hn
  rw [F.map_id] at hn
  have h := congrArg (fun z ↦
    ((F.obj A ◁ e.hom) ▷ F.obj U) ≫ z ≫
      F.map (T.map (Prod.mkHom (𝟙 A) l.hom))) (ha A)
  simp only [Category.assoc, ← F.map_comp, ht] at h
  have hn' := μ.hom.naturality (Prod.mkHom (𝟙 A) l.hom)
  change (tensor D).map (Prod.mkHom (F.map (𝟙 A)) (F.map l.hom)) ≫
    μ.hom.app (A, U) = μ.hom.app (A, T.obj (U, U)) ≫
      F.map (T.map (Prod.mkHom (𝟙 A) l.hom)) at hn'
  rw [F.map_id] at hn'
  rw [← hn', ← hn] at h
  simp only [tensor_map, id_tensorHom, tensorHom_id] at h hl ⊢
  have he := associator_naturality (𝟙 (F.obj A)) e.hom (𝟙 (F.obj U))
  simp only [tensorHom_id, id_tensorHom] at he
  rw [← Category.assoc ((F.obj A ◁ e.hom) ▷ F.obj U)
    (α_ (F.obj A) (F.obj U) (F.obj U)).hom, he] at h
  simp only [Category.assoc] at h
  rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc] at h
  simp only [Category.assoc, hl, triangle_assoc] at h
  change ((F.obj A ◁ e.hom ≫ μ.hom.app (A, U) ≫ F.map (r A).hom) ▷ F.obj U) ≫
    μ.hom.app (A, U) = (ρ_ (F.obj A)).hom ▷ F.obj U ≫ μ.hom.app (A, U)
  simpa only [comp_whiskerRight, Category.assoc] using h

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  (R : LocallyFiniteAdicRealization.Realization l X)
  [∀ x : X, Invertible (l : X.residueField x)]
  (closed : CoefficientClosedStructure (ambientHom l X R))
  (models : CoefficientTensorModels.{u + 1, u + 1, u}
    (ProEt.topology X) (ring l X R) closed)
  (symmetry : @SymmetricCategory _ _ closed.monoidal)

/-- Arbitrary unit comparisons cannot all satisfy the right-unit law when the
native tensor unit has a nonidentity automorphism.
Source: cancellation in the monoidal functor unit equation, using the unit object
of BS Remark 6.8.15; Mathlib's left-unitor natural isomorphism.
(blueprint: lem-sf-adic-completed-tensor-right-unit-not-universal).

Proof: fix the tensorator and compare data.unit with e followed by data.unit.
If the universal equation held, its instances at the common coefficient unit
would identify the two tensor maps after the same tensorator and mapped right
unitor. Their composite is invertible, so cancel it. Tensoring on the left by
the ordinary image of the coefficient unit is faithful, because data.unit
identifies that image with the native tensor unit. Hence the unit maps agree.
Cancel data.unit to deduce that e is the identity, contrary to the hypothesis.
No nonemptiness or characteristic hypothesis is hidden: the nonidentity
unit automorphism is supplied explicitly; the empty scheme need not admit one. -/
theorem completed_tensor_common_lift_right_unit_not_universal
    (data : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry)
    (e : closed.monoidal.tensorUnit ≅ closed.monoidal.tensorUnit)
    (he : e.hom ≠ 𝟙 _) :
    ¬ (∀ d : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry,
      ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
        closed.tensor.map (Prod.mkHom (𝟙 _) d.unit.hom) ≫
            d.tensor.hom.app (A, pullbackTensorCommonUnit l (PadicAlgCl l) X) ≫
            (ordinary l X R).map
              (pullbackTensorCommonRightUnitor l (PadicAlgCl l) X A).hom =
          (closed.monoidal.rightUnitor ((ordinary l X R).obj A)).hom) := by
  let := closed.monoidal
  intro h
  let U := pullbackTensorCommonUnit l (PadicAlgCl l) X
  let d : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry :=
    { data with unit := e ≪≫ data.unit }
  obtain ⟨a, _, unique⟩ :=
    completed_tensor_common_lift_unit_normalization l X R closed models symmetry data
  have hu : data.unit.hom = d.unit.hom := congrArg Iso.hom
    ((unique data.unit (h data U)).trans (unique d.unit (h d U)).symm)
  apply he
  apply (cancel_mono data.unit.hom).1
  simpa only [d, Iso.trans_hom, Category.id_comp] using hu.symm

-- STATEMENT-DISPUTED: data.unit is arbitrary, so the equation is asserted for every
-- isomorphism from the native unit. The theorem just above refutes that universal
-- assertion whenever the native unit has a nonidentity automorphism. In a nonzero
-- characteristic-zero coefficient category, negation supplies such an automorphism.
-- The finite models N and native coherence do not constrain data.unit or data.tensor.
/-- The right-unit component of the common-stage constraint system.
The finite coefficient multiplication calculation and its transport through the
native right unitor are the proof obligations isolated here.
(blueprint: new-sf-adic-completed-tensor-common-lift-constraints-right-unit). -/
theorem completed_tensor_common_lift_constraints_right_unit
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry)
    (data : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry) :
    ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
      closed.tensor.map (Prod.mkHom (𝟙 _) data.unit.hom) ≫
          data.tensor.hom.app (A, pullbackTensorCommonUnit l (PadicAlgCl l) X) ≫
          (ordinary l X R).map (pullbackTensorCommonRightUnitor l (PadicAlgCl l) X A).hom =
        (closed.monoidal.rightUnitor ((ordinary l X R).obj A)).hom := by
  let := closed.monoidal
  exact right_unit_of_left_associativity (ordinary l X R)
    (commonStageDerivedTensor l (PadicAlgCl l) X)
    (pullbackTensorCommonUnit l (PadicAlgCl l) X)
    (fun A ↦ pullbackTensorCommonAssociator l (PadicAlgCl l) X A
      (pullbackTensorCommonUnit l (PadicAlgCl l) X)
      (pullbackTensorCommonUnit l (PadicAlgCl l) X))
    (pullbackTensorCommonLeftUnitor l (PadicAlgCl l) X
      (pullbackTensorCommonUnit l (PadicAlgCl l) X))
    (pullbackTensorCommonRightUnitor l (PadicAlgCl l) X) data.tensor data.unit
    (fun A ↦ commonStageTensor_triangle l (PadicAlgCl l) X A
      (pullbackTensorCommonUnit l (PadicAlgCl l) X))
    (fun A ↦ completed_tensor_common_lift_constraints_associative l X R closed models
      symmetry N coherence data A (pullbackTensorCommonUnit l (PadicAlgCl l) X)
      (pullbackTensorCommonUnit l (PadicAlgCl l) X))
    (completed_tensor_common_lift_constraints_left_unit l X R closed models symmetry
      N coherence data (pullbackTensorCommonUnit l (PadicAlgCl l) X))

end WeilConjectures.AdicQbarRealization
