/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralProjectionEvaluationFactors

/-! # Finite intrinsic tensor realization

This isolates the existence of the coefficient realization family used by the
finite intrinsic projection comparison.

Source: fix-prop-projection-formula.proof.md, comparison of the same projection map.
(blueprint: new-sf-finite-intrinsic-tensor-realization).

Proof: construct the normalized constant coefficient tensor comparison on simultaneous
flat K-flat representatives, and descend it through the derived localization. The
comparison is natural in both inputs and is an isomorphism at every ambient finite
input. This is the tensor realization part of the finite projection argument; no
support, compactification, or projection map is involved.
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

/-- The normalized family of finite intrinsic-to-fixed tensor comparisons.

(blueprint: new-sf-finite-intrinsic-tensor-realization).

Proof: construct the normalized constant-coefficient tensor comparison on simultaneous flat
K-flat representatives and descend it through the derived localization. The comparison is
natural in both inputs and is an isomorphism at every ambient finite input. -/
theorem finiteIntrinsicTensorRealization
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    (S : SixFunctorFiniteOperations D C E (m + 1) (Nat.le_add_left 1 m)) :
    Nonempty (∀ X : SixFunctorSpace D,
        finiteIntrinsicDerivedTensor C.l E X.obj.left m ≅
          evaluatedTensor (C := C) (E := E) m X) := by sorry

end WeilConjectures.IntegralProjectionReduction
