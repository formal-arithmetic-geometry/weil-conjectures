/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointEvaluation.PointEvaluationTensorData

/-! # Signed tensor coherence for point sections

Source: Stacks Project, sites-cohomology.tex, Tag 07A4, and sites-modules.tex,
Tag 03EL; normalized point specialization in the relative Kunneth proof
(blueprint: def-sf-point-evaluation-tensor-coherence).

The four fields are equalities of the existing signed direct-sum total-complex
chain maps. The associator preserves the order of homogeneous generators, the
cochain braiding exchanges degrees i and j with sign (-1)^(ij), and the action
unitors multiply scalars. No new tensor or monoidal structure is introduced.
-/

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

namespace AlgebraicGeometry.ProEtale.PointEvaluation

variable {k : Type u} [Field k]
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})

/-- Associativity, signed symmetry and both action-unit equations for the normalized
point-section comparison. These are chain-map equalities for all unbounded complexes,
using the existing generator-order associator, Koszul braiding and scalar-action unitors.
Source: Stacks 07A4 and 03EL; relative Kunneth point specialization
(blueprint: def-sf-point-evaluation-tensor-coherence). -/
structure TensorCoherent (T : TensorModel B) : Prop where
  /-- The two triple-tensor routes agree, without permuting generators. -/
  associativity : ∀ P Q H : Complexes B,
    (complexSections k B).map
      (HomologicalComplex.associator.{u + 1, u + 2, 0} (C := ModuleSheaves B) P Q H).hom ≫ (T.b P
        (totalObj B Q H)).hom ≫
        (𝟙 _ ⊗ₘ (T.b Q H).hom) =
      (T.b (totalObj B P Q) H).hom ≫ ((T.b P Q).hom ⊗ₘ 𝟙 _) ≫
        (α_ ((complexSections k B).obj P) ((complexSections k B).obj Q)
          ((complexSections k B).obj H)).hom
  /-- The comparison commutes with exchange carrying the Koszul sign (-1)^(ij). -/
  symmetry : ∀ P Q : Complexes B,
    (complexSections k B).map (CochainComplex.Monoidal.braiding.{u + 1, u + 2} (C := ModuleSheaves
      B) P Q).hom ≫ (T.b Q P).hom =
      (T.b P Q).hom ≫ (CochainComplex.Monoidal.braiding
        ((complexSections k B).obj P) ((complexSections k B).obj Q)).hom
  /-- The left action unitor agrees with comparison followed by the unit map. -/
  left_unit : ∀ P : Complexes B, (complexSections k B).map (HomologicalComplex.leftUnitor.{u + 1,
    u + 2, 0} (C := ModuleSheaves B) P).hom =
    (T.b (complexUnit B) P).hom ≫ (T.unit.hom ⊗ₘ 𝟙 _) ≫ (λ_ ((complexSections k B).obj P)).hom
  /-- The right action unitor agrees with comparison followed by the unit map. -/
  right_unit : ∀ P : Complexes B, (complexSections k B).map (HomologicalComplex.rightUnitor.{u +
    1, u + 2, 0} (C := ModuleSheaves B) P).hom =
    (T.b P (complexUnit B)).hom ≫ (𝟙 _ ⊗ₘ T.unit.hom) ≫ (ρ_ ((complexSections k B).obj P)).hom

end AlgebraicGeometry.ProEtale.PointEvaluation
