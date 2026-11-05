/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.CategoryTheory.SmoothPurity.AdicBasisLimit
import WeilConjectures.NumberTheory.Padics.LocalFieldIntegralBasis
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # Finite freeness of the specified completed integral coefficient inclusion

The coefficient and site universes are independent. The coefficient map is fixed by its
finite reductions, so the transported basis has the specified scalar action.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-weil-completed-integral-finite-free).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
universe t u a b r
open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
namespace WeilConjectures
section RingTransport
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{r}}

end RingTransport
section IntegralBasis

variable (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

end IntegralBasis

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})

attribute [local instance] scalarPreservesSheafification

variable (L : Type u) [Field L] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

end WeilConjectures
