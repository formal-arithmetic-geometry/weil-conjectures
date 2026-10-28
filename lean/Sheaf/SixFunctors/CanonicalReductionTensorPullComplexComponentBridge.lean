/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge
public import Sheaf.Paper.TensorReductionStrictComparison
public import Sheaf.Paper.CompletedPullbackTowerRealizations

/-! # Finite-evaluation bridge for the ordinary reduction/tensor pullback component

Source: Stacks 07A4, 07A6 and 0941; lem-fix-operation-reduction, first paragraph.
-/

@[expose] public section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory

/--
The finite-evaluation equations for the strict reduction maps are sufficient for
one degree of the ordinary reduction/tensor pullback square.  This is the
finite-level bridge used to assemble the degreewise identity; its proof is the
pure-tensor calculation together with the normalized unit formula for the
sequence pullback tensor comparison.

Source: Stacks 07A4, 07A6 and 0941; the first paragraph of
`lem-fix-operation-reduction`, after finite evaluation and before cochain
extensionality.  The two hypotheses are exactly the finite-component
characterizations of `tensorReductionStrictMap` at the source and target.
(blueprint: lem-sf-canonical-reduction-tensor-pull-complex-component-bridge).
-/
theorem canonicalReductionTensorPullComplex_component_bridge
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (a : OrdinaryLimitModel l E) {U V : Scheme.{u}} (f : U ⟶ V)
    (P Q : CochainComplex (integralTowerModules l E V) ℤ) (n : ℤ)
    (hV : ∀ m : ℕ,
      ((coefficientSequenceEvaluation l E V m).mapHomologicalComplex (.up ℤ)).map
        (tensorReductionStrictMap l E V P Q) =
        tensorReductionFiniteComponent l E V P Q m)
    (hU : ∀ m : ℕ,
      ((coefficientSequenceEvaluation l E U m).mapHomologicalComplex (.up ℤ)).map
        (tensorReductionStrictMap l E U
          (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P)
          (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj Q)) =
        tensorReductionFiniteComponent l E U
          (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P)
          (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj Q) m) :
    let F := (integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)
    let R (W : Scheme.{u}) :=
      (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let S := (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
    let T := (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology V)
      (completedIntegralCommRingSheafUnrestricted l E V)).obj (P, Q)
    (a.reductionPullComplex l E f T ≫
        S.map (tensorReductionStrictMap l E V P Q) ≫
        (pullbackTensorSequenceCochain l E f).hom.app ((R V).obj P, (R V).obj Q)).f n =
      ((R U).map
          (proEtaleTensorPullbackTotalIso f ((PurCompactSupport.completed l E).ring V)
            ((PurCompactSupport.completed l E).ring U)
            ((PurCompactSupport.completed l E).pull f) P Q).inv ≫
        tensorReductionStrictMap l E U (F.obj P) (F.obj Q) ≫
        (coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology U))
          (coefficientSequenceCommRingSheaf l E U)).map
          (Prod.mkHom (a.reductionPullComplex l E f P)
            (a.reductionPullComplex l E f Q))).f n := by
  sorry

end WeilConjectures.IntegralSystemRealization
