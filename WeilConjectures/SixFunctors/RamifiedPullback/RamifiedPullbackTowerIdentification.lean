/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedPullbackTowerData
import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedCoefficientQuotientComparison
import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedFinitePullbackComparison
import WeilConjectures.SixFunctors.RamifiedPullback.FinitePullbackTransitionGenerators
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralProjectionDivisibility

/-! # Ramified identification of finite pullback towers

The arithmetic construction and factorization of the normalized finite comparison.
Source: Stacks 093M, 03EK, 03EL; Bhatt--Scholze 6.8.2(1).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.RamifiedPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

end WeilConjectures.RamifiedPullback
