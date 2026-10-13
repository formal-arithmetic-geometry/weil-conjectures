/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryEvaluationData

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

/-- Projected evaluation respects arbitrary precomposition maps and scalars.
Source: Stacks Project, Tag 08DQ, proof of lemma-dual-perfect-complex;
Tag 03EO, tensor-Hom adjunction.
(blueprint: lem-pc-ordinary-evaluation-precomposition-naturality).
Proof: expand both nonzero component formulas. Naturality of tensor-Hom
moves the source map a through currying and through the braiding and
associator. The assumed projection identity then replaces a followed by
the dual projection with z times the original projection and precomposition
by f. Naturality of uncurrying in the Hom input moves f to the input of the
outer evaluation; currying sends this to homObjMap f. Additivity moves z
outside tensoring and currying. Output naturality composes the canonical
transports p=s+n and s+n=r+m to the canonical transport p=r+m.
All index equalities are proof-irrelevant. Neither complex need be bounded,
and zero modules satisfy the same naturality equations. -/
theorem ordinaryEvaluation_precomposition_naturality (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (p q q' n m r s : ℤ) (hpq : p + q = n) (hpq' : p + q' = m)
    (hr : r + q' = 0) (hs : s + q = 0) (ht : s + n = r + m)
    (f : P.X r ⟶ P.X s)
    (a : (localEvaluationDual X U P).X q ⟶ (localEvaluationDual X U P).X q')
    (z : ℤˣ)
    (ha : a ≫ localEvaluationProjection X U P (localEvaluationUnit X U) q' r 0 hr =
      z • (localEvaluationProjection X U P (localEvaluationUnit X U) q s 0 hs ≫
        SheafOfModules.homObjMap (R := X.sheaf.over U) f
          (𝟙 ((localEvaluationUnit X U).X 0)))) :
    (F.X p ◁ a) ≫ localEvaluationComponent X U P F p q' m r hpq' =
      z • (localEvaluationComponent X U P F p q n s hpq ≫
        SheafOfModules.homObjMap (R := X.sheaf.over U) f (F.XIsoOfEq ht).hom) := by sorry

end AlgebraicGeometry
