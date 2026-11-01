/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientHomChange
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorNormalizationUnit
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorNormalizationTower
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorNormalizationQuotient
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorNormalizationFinite
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorNormalizationScalar

/-! # Normalization of the canonical coefficient tensor comparisons

Source: current blueprint, sec-six-functors/sk-thm-sf-compatibility,
fix-prop-coherence.proof.md, tensor reassociation and evaluation sentence.
(blueprint: lem-sf-coefficient-tensor-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

end WeilConjectures
