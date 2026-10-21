/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module
public import Sheaf.SixFunctors.PointEvaluationTensorData

/-! Source: Stacks 0991, 03EL, 07A4
(blueprint: def-sf-point-evaluation-tensor-coherence). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
set_option linter.unusedVariables false
attribute [local irreducible] SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.CochainPullback
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.ProEtale.PointEvaluation
variable {k : Type u} [Field k]
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
/-- The signed chain coherence equations for the specified comparison.
Source: Stacks 03EL, 07A4 (blueprint: def-sf-point-evaluation-tensor-coherence). -/
structure TensorCoherent (T : TensorModel B) : Prop where
  /-- The signed total associator preserves generator order. -/
  associativity : ∀ P Q H : Complexes B,
    (complexSections k B).map
      (HomologicalComplex.associator.{u + 1, u + 2, 0} (C := ModuleSheaves B) P Q H).hom ≫ (T.b P
        (totalObj B Q H)).hom ≫
        (𝟙 _ ⊗ₘ (T.b Q H).hom) =
      (T.b (totalObj B P Q) H).hom ≫ ((T.b P Q).hom ⊗ₘ 𝟙 _) ≫
        (α_ ((complexSections k B).obj P) ((complexSections k B).obj Q)
          ((complexSections k B).obj H)).hom
  /-- This is Mathlib's Koszul braiding, with coefficient (-1)^(ij). -/
  symmetry : ∀ P Q : Complexes B,
    (complexSections k B).map (CochainComplex.Monoidal.braiding.{u + 1, u + 2} (C := ModuleSheaves
      B) P Q).hom ≫ (T.b Q P).hom =
      (T.b P Q).hom ≫ (CochainComplex.Monoidal.braiding
        ((complexSections k B).obj P) ((complexSections k B).obj Q)).hom
  /-- Left action unitor, as an equality of chain maps. -/
  left_unit : ∀ P : Complexes B, (complexSections k B).map (HomologicalComplex.leftUnitor.{u + 1,
    u + 2, 0} (C := ModuleSheaves B) P).hom =
    (T.b (complexUnit B) P).hom ≫ (T.unit.hom ⊗ₘ 𝟙 _) ≫ (λ_ ((complexSections k B).obj P)).hom
  /-- Right action unitor, as an equality of chain maps. -/
  right_unit : ∀ P : Complexes B, (complexSections k B).map (HomologicalComplex.rightUnitor.{u +
    1, u + 2, 0} (C := ModuleSheaves B) P).hom =
    (T.b P (complexUnit B)).hom ≫ (𝟙 _ ⊗ₘ T.unit.hom) ≫ (ρ_ ((complexSections k B).obj P)).hom


end AlgebraicGeometry.ProEtale.PointEvaluation
