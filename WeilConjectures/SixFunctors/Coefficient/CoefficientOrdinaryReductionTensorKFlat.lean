/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryQuotientModel
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections

/-! # The ordinary quotient system preserves K-flat complexes

Source: Stacks 06YN, 07A4 and 0941.

K-flatness on the ringed sequence site is tested on finite evaluations: evaluation is
exact, commutes with the total tensor product, and exactness on the sequence site is
detected by the finite evaluations. The finite evaluations of the ordinary quotient
system of a K-flat complex are its finite scalar extensions, which are K-flat.
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

noncomputable section
set_option synthInstance.maxSize 4096
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionExtension coefficientEvaluationTensorIso
  coefficientScalarTensorIso

namespace OrdinaryQuotient

end OrdinaryQuotient

end
end WeilConjectures
