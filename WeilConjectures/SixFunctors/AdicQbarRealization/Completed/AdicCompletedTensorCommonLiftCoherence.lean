/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorFiniteModels
public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonComponent
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonLiftConstraintsAssociative
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonLiftConstraintsLeftUnit
import WeilConjectures.SixFunctors.Common.CommonStageTensorTriangle
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonLiftConstraintsSymmetric
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonLiftNormalizedTensorUnit

/-! # Coherence part of the common-stage completed tensor lift

This module isolates the common-stage tensorator, unit, and its four constraint
equations and retains the common-field construction formula.
Finite-stage agreement with that formula is proved in the companion module.
The split follows the finite normalization argument in BS Remark 6.8.15 and HRS
Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-common-lift-coherence).
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

/-- Common-stage tensor and monoidal constraint data with its construction formula.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-common-lift-coherence). -/
structure CompletedTensorCommonLiftCoherence
    (models : CoefficientTensorModels.{u + 1, u + 1, u}
      (ProEt.topology X) (ring l X R) closed)
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E) where
  tensor : ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor ≅
    commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R
  /-- Retain the actual common-field construction, before proving finite agreement. -/
  tensor_eq : ∀ P Q, tensor.hom.app (P, Q) =
    (completedTensorCommonComponent l X R closed models N P Q).hom
  unit : closed.monoidal.tensorUnit ≅
    (ordinary l X R).obj (pullbackTensorCommonUnit l (PadicAlgCl l) X)
  associative : ∀ A B C : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom (tensor.hom.app (A, B)) (𝟙 _)) ≫
        tensor.hom.app ((commonStageDerivedTensor l (PadicAlgCl l) X).obj (A, B), C) ≫
        (ordinary l X R).map (pullbackTensorCommonAssociator l (PadicAlgCl l) X A B C).hom =
      (closed.monoidal.associator ((ordinary l X R).obj A) ((ordinary l X R).obj B)
        ((ordinary l X R).obj C)).hom ≫
        closed.tensor.map (Prod.mkHom (𝟙 _) (tensor.hom.app (B, C))) ≫
        tensor.hom.app (A, (commonStageDerivedTensor l (PadicAlgCl l) X).obj (B, C))
  left_unit : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom unit.hom (𝟙 _)) ≫
        tensor.hom.app (pullbackTensorCommonUnit l (PadicAlgCl l) X, A) ≫
        (ordinary l X R).map (pullbackTensorCommonLeftUnitor l (PadicAlgCl l) X A).hom =
      (closed.monoidal.leftUnitor ((ordinary l X R).obj A)).hom
  right_unit : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom (𝟙 _) unit.hom) ≫
        tensor.hom.app (A, pullbackTensorCommonUnit l (PadicAlgCl l) X) ≫
        (ordinary l X R).map (pullbackTensorCommonRightUnitor l (PadicAlgCl l) X A).hom =
      (closed.monoidal.rightUnitor ((ordinary l X R).obj A)).hom
  symmetric : ∀ A B : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    tensor.hom.app (A, B) ≫
        (ordinary l X R).map (pullbackTensorCommonBraiding l (PadicAlgCl l) X A B).hom =
      (symmetry.braiding ((ordinary l X R).obj A) ((ordinary l X R).obj B)).hom ≫
        tensor.hom.app (B, A)

/-- The normalized common-stage coherence data exists under native derived coherence.
The finite tensor comparison and its integral agreement are isolated in the companion
lemma `completed_tensor_common_lift_agreement`.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-common-lift-coherence). -/
theorem completed_tensor_common_lift_coherence
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry) :
    Nonempty (CompletedTensorCommonLiftCoherence l X R closed symmetry models N) := by
  obtain ⟨data, hdata⟩ :=
    completed_tensor_common_lift_normalized_tensor_unit l X R closed models symmetry N coherence
  exact ⟨{ tensor := data.tensor
           tensor_eq := hdata
           unit := data.unit
           associative := completed_tensor_common_lift_constraints_associative l X R closed
             models symmetry N coherence data hdata
           left_unit := completed_tensor_common_lift_constraints_left_unit l X R closed models
             symmetry N coherence data
           right_unit := by
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
                 symmetry N coherence data hdata A (pullbackTensorCommonUnit l (PadicAlgCl l) X)
                 (pullbackTensorCommonUnit l (PadicAlgCl l) X))
               (completed_tensor_common_lift_constraints_left_unit l X R closed models symmetry
                 N coherence data (pullbackTensorCommonUnit l (PadicAlgCl l) X))
           symmetric := completed_tensor_common_lift_constraints_symmetric l X R closed models
             symmetry N coherence data hdata }⟩

end WeilConjectures.AdicQbarRealization
