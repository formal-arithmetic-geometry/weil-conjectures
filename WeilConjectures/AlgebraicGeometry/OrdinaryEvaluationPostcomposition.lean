/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationComponentFactorization

/-! # Ordinary evaluation postcomposition

Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
(blueprint: lem-pc-ordinary-evaluation-postcomposition).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

@[reassoc] private theorem evaluation_postcomposition {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (E B B' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (a : B ⟶ B') :
    a ▷ SheafOfModules.homObj (R := R) E (𝟙_ _) ≫
        SheafOfModules.moduleDualEvaluation R E B' =
      SheafOfModules.moduleDualEvaluation R E B ≫
        SheafOfModules.homObjMap (R := R) (𝟙 E) a := by
  unfold SheafOfModules.moduleDualEvaluation
  rw [← SheafOfModules.tensorHomEquiv_whiskerLeft_comp (R := R),
    ← SheafOfModules.tensorHomEquiv_comp_homObjMap (R := R)]
  apply (SheafOfModules.tensorHomEquiv (R := R) E _ B').congr_arg
  rw [BraidedCategory.braiding_naturality_right_assoc,
    associator_naturality_left_assoc, ← whisker_exchange_assoc,
    rightUnitor_naturality]
  simp only [Category.assoc]

end AlgebraicGeometry
