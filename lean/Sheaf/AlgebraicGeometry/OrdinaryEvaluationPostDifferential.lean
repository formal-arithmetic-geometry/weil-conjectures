/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.BoundedOrdinaryEvaluationAssembly

/-! # Ordinary evaluation and one part of the differential

Source: Stacks Project, Tag 08DQ, and Section 20.41.
(blueprint: lem-pc-ordinary-evaluation-post-differential).
-/

@[expose] public section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

local instance ordinaryPostMonoidalPreadditive (X : Scheme.{u}) (U : X.Opens) :
    MonoidalPreadditive (localEvaluationModules X U) :=
  Classical.choice (SheafOfModules.tensorClosed (X.sheaf.over U)).1

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 800000 in
-- Naturality rewrites involve the expanded sheaf tensor and internal Hom instances.
/-- Evaluation commutes with the differential in the output complex.
Source: Stacks Project, Tag 08DQ, ordinary evaluation calculation, and Section 20.41.
(blueprint: lem-pc-ordinary-evaluation-post-differential).

Proof: If r+q is nonzero, both evaluation components vanish. Otherwise p=r+n
and p+1=r+m. Expand the component definition, and move d_F across the
right unitor, the associator and the braidings by naturality. Naturality of
the tensor-Hom equivalence in its output identifies postcomposition by d_F
with the whiskered differential on F. Degree transports agree by proof
irrelevance. This uses no boundedness and also holds for zero modules. -/
theorem ordinaryEvaluation_post_differential (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (n m p q r : ℤ) (hnm : n + 1 = m) (hpq : p + q = n) :
    localEvaluationComponent X U P F p q n r hpq ≫
        SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X r)) (F.d (r + n) (r + m)) =
      (F.d p (p + 1) ▷ (localEvaluationDual X U P).X q) ≫
        localEvaluationComponent X U P F (p + 1) q m r (by omega)  := by
  classical
  by_cases h : r + q = 0
  · simp only [localEvaluationComponent, dif_pos h]
    rw [← SheafOfModules.tensorHomEquiv_comp_homObjMap (R := X.sheaf.over U),
      ← SheafOfModules.tensorHomEquiv_whiskerLeft_comp (R := X.sheaf.over U)]
    apply (SheafOfModules.tensorHomEquiv (R := X.sheaf.over U) (P.X r) _ _).congr_arg
    simp only [Category.assoc, HomologicalComplex.XIsoOfEq_hom_comp_d F]
    rw [BraidedCategory.braiding_naturality_right_assoc,
      associator_naturality_left_assoc]
    rw [← whisker_exchange_assoc, rightUnitor_naturality_assoc]
    simp only [HomologicalComplex.d_comp_XIsoOfEq_hom F]
  · simp only [localEvaluationComponent, dif_neg h, zero_comp, comp_zero]

end AlgebraicGeometry
