/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.BoundedOrdinaryEvaluationAssembly

/-! # The ordinary evaluation differential on one tensor summand

Source: Stacks Project, Tag 08DQ, and Section 20.41.
(blueprint: lem-pc-ordinary-evaluation-differential-summand).
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

local instance ordinarySummandMonoidalPreadditive (X : Scheme.{u}) (U : X.Opens) :
    MonoidalPreadditive (localEvaluationModules X U) :=
  Classical.choice (SheafOfModules.tensorClosed (X.sheaf.over U)).1

/-- On a single tensor summand, evaluation satisfies the projected differential equation.
Source: Stacks Project, Tag 08DQ, ordinary complex comparison; Section 20.41,
Hom-complex differential.
(blueprint: lem-pc-ordinary-evaluation-differential-summand).

Proof: Use the specified component formula for the graded maps e. On the summand
F^p tensor D^q, the total differential is d_F tensor 1 plus (-1)^p times
1 tensor d_D. Expand the differential of Hom(P,F) after its rth projection:
postcomposition with d_F minus (-1)^n precomposition with d_P. For r+q=0,
only the d_F terms remain; evaluation and the right unit action are natural
in F, so these terms agree. For r+q=-1, only the d_P terms remain. Expand
the Hom differential of D=Hom(P,O[0]); the differential of O[0] vanishes,
so it is -(-1)^q times precomposition with d_P. Naturality in P identifies
these contributions and (-1)^p (-1)^q=(-1)^(p+q)=(-1)^n gives the sign.
For every other r+q, both component formulas are zero. The degree transports
agree by proof irrelevance. These arguments apply to zero terms and empty
opens; no boundedness or perfectness is used. This is only a calculation on
one summand and one projection, without assembling the global equation. -/
theorem ordinaryEvaluation_differential_summand (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (e : ∀ n : ℤ, (localEvaluationTensor X U P F).X n ⟶
      (homComplex (R := X.sheaf.over U) P F).X n)
    (he : ∀ (p q n r : ℤ) (h : p + q = n),
      HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
          (curriedTensor _) (.up ℤ) p q n h ≫ e n ≫
        localEvaluationProjection X U P F n r (r + n) rfl =
          localEvaluationComponent X U P F p q n r h)
    (n m p q r : ℤ) (hnm : (ComplexShape.up ℤ).Rel n m) (hpq : p + q = n) :
    HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
        (curriedTensor _) (.up ℤ) p q n hpq ≫ e n ≫
      (homComplex (R := X.sheaf.over U) P F).d n m ≫
      localEvaluationProjection X U P F m r (r + m) rfl =
    HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
        (curriedTensor _) (.up ℤ) p q n hpq ≫
      (localEvaluationTensor X U P F).d n m ≫ e m ≫
      localEvaluationProjection X U P F m r (r + m) rfl := by sorry

end AlgebraicGeometry
