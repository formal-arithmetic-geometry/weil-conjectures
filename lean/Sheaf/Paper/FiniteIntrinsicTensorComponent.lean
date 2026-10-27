/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralProjectionEvaluationFactors
import Sheaf.SixFunctors.ProEtaleIntrinsicTensorComparison
import Sheaf.AlgebraicGeometry.IntrinsicRealizationTensorComplex
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # Pointwise finite intrinsic tensor comparison

This is the pointwise construction step for the finite intrinsic tensor realization.

Source: fix-prop-projection-formula.proof.md, comparison of the same projection map;
Stacks 03EK, 03EL, 06YS and 07A4.
(blueprint: lem-sf-finite-intrinsic-tensor-component).

The pointwise statement isolates the simultaneous flat K-flat representative calculation
before assembling the resulting comparisons into a family indexed by all six-functor spaces.
The proof uses the intrinsic tensor comparison, its total-complex realization, and the
independent-coefficient K-flat resolution theorem. It retains the exact finite coefficient
and ambient derived tensor objects occurring in the parent statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus CompactSupportFiniteProjection.tensor
  sfIntrinsicDerivedEquivalence

/-- Pointwise finite intrinsic-to-fixed tensor comparison.

(blueprint: lem-sf-finite-intrinsic-tensor-component).

Proof: choose independent-coefficient flat K-flat representatives of the two inputs,
apply the intrinsic right-tensor comparison in every bidegree, use the total-complex
realization isomorphism, and descend the normalized comparison through the derived
localization. The resulting comparison is invertible for the fixed finite coefficient
level and the chosen ambient six-functor space.
-/
theorem finiteIntrinsicTensorRealization_component
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    (X : SixFunctorSpace D) :
    Nonempty (finiteIntrinsicDerivedTensor C.l E X.obj.left m ≅
      evaluatedTensor (C := C) (E := E) m X) := by
  sorry

end WeilConjectures.IntegralProjectionReduction
