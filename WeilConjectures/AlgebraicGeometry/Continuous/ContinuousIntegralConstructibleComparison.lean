/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousIntegralSliceModelComparison
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousIntegralCoefficientComparison

/-!
# Continuous and completed integral constructibility

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3).
(blueprint: lem-weil-pbc-continuous-integral-constructible-comparison)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

universe u₁ v₁ w₁ a₁

end AlgebraicGeometry.ProEtale
