/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.AlgebraicGeometry.OrdinaryEvaluationData
import Sheaf.AlgebraicGeometry.OrdinaryEvaluationComponentFactorization

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

/-- Ordinary evaluation is natural in the coefficient complex.
Source: Stacks Project, cohomology.tex, Tag 08DJ (lemma-internal-hom) and
Tag 08DQ (lemma-dual-perfect-complex), component calculation.
(blueprint: lem-pc-ordinary-evaluation-postcomposition).

Proof: Use chain-map extensionality, total tensor coproduct inclusions in degrees
(p,q), and the Hom product projections indexed by r. Naturality of tensor inclusions
changes the source coefficient by t.f p. Naturality of the Hom projection changes
the target by t.f (r+n). Substitute hf and hf' on the two sides. When r+q is nonzero
both components vanish. Otherwise expand localEvaluationComponent. Naturality of
the tensor-Hom equivalence, associator, braiding and right unitor moves t.f p
through evaluation. The chain-object transport to degree r+n is natural, so the
components agree. The projections and inclusions are jointly detecting. -/
theorem ordinaryEvaluation_postcomposition (X : Scheme.{u}) (U : X.Opens)
    (P F F' : CochainComplex (localEvaluationModules X U) ℤ) (t : F ⟶ F')
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (f' : localEvaluationTensor X U P F' ⟶ homComplex (R := X.sheaf.over U) P F')
    (hf : IsLocalOrdinaryEvaluation X U P F f)
    (hf' : IsLocalOrdinaryEvaluation X U P F' f') :
    HomologicalComplex.mapBifunctorMap t (𝟙 (localEvaluationDual X U P))
      (curriedTensor _) (.up ℤ) ≫ f' =
        f ≫ ((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t := by sorry

end AlgebraicGeometry
