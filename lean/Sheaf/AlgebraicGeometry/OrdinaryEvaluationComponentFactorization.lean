/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryEvaluationData

/-! # Factorization of ordinary evaluation components

Source: Stacks Project, Tag 08DQ, and Section 20.41.
(blueprint: lem-pc-ordinary-evaluation-component-factorization).
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

/-- Factorization of a nonzero ordinary evaluation component through module evaluation.
Source: Stacks Project, Tag 08DQ, ordinary evaluation map; Tag 03EO, tensor-Hom
adjunction naturality.
(blueprint: lem-pc-ordinary-evaluation-component-factorization).
Proof: Since r+q=0, the positive branch of localEvaluationComponent applies. Write b
for its dual projection followed by the degree-zero unit identification, and g for
its output degree transport. Naturality of tensorHomEquiv in the tensor argument
moves F^p tensor b inside currying; naturality in the output moves g inside currying.
Expand moduleDualEvaluation. Braiding naturality moves b from the outer tensor input
past the first braiding, associator naturality moves it through the associator, and
braiding naturality moves it past the inner braiding. The remaining equality is
uncurry(b)= (P^r tensor b) followed by uncurry(id), proved by applying the injective
currying equivalence and using its tensor-input naturality and inverse laws.
Reassociate compositions to recover exactly the positive component formula.
The index-equality proofs are irrelevant; zero objects and arbitrary unbounded
complexes satisfy the same identities. -/
theorem ordinaryEvaluation_component_factorization (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (p q n r : ℤ) (hpq : p + q = n) (hr : r + q = 0) :
    localEvaluationComponent X U P F p q n r hpq =
      (F.X p ◁ (localEvaluationProjection X U P (localEvaluationUnit X U) q r 0 hr ≫
        SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X r))
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (𝟙_ (localEvaluationModules X U))).hom)) ≫
      SheafOfModules.moduleDualEvaluation.{u}
        (C := Over U) (J := (Opens.grothendieckTopology X).over U) (X.sheaf.over U)
        (P.X r) (F.X p) ≫
      SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X r))
        (F.XIsoOfEq (by omega : p = r + n)).hom := by sorry

end AlgebraicGeometry
