/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationComponentFactorization

/-! # Ordinary evaluation and one part of the differential

Source: Stacks Project, Tag 08DQ, and Section 20.41.
(blueprint: lem-pc-ordinary-evaluation-precomposition-naturality).
-/

@[expose] public section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

@[reassoc] private theorem evaluation_naturality
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    {E H : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (B : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (f : E ⟶ H) :
    B ◁ SheafOfModules.homObjMap (R := R) f (𝟙 (𝟙_ _)) ≫
        SheafOfModules.moduleDualEvaluation (R) E B =
      SheafOfModules.moduleDualEvaluation (R) H B ≫
        SheafOfModules.homObjMap (R := R) f (𝟙 B) := by
  unfold SheafOfModules.moduleDualEvaluation
  rw [← SheafOfModules.tensorHomEquiv_whiskerLeft_comp (R := R),
    ← SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := R)]
  apply (SheafOfModules.tensorHomEquiv (R := R) E _ B).congr_arg
  rw [BraidedCategory.braiding_naturality_right_assoc,
    associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
    BraidedCategory.braiding_naturality_left_assoc, evaluation_precomposition R]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [BraidedCategory.braiding_naturality_left_assoc,
    associator_naturality_right_assoc]
  simp only [← whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_right_assoc]

end AlgebraicGeometry
