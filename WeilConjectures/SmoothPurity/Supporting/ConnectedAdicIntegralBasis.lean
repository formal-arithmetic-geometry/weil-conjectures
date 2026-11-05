/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralScalarData
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Constant values and prescribed integral bases on connected schemes

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 4.2.12,
Definition 6.8.1 and Lemma 6.8.2(1), printed pp. 30 and 58--59
(blueprint: lem-pur-connected-adic-integral-basis).

The positive quotient exponent is n+1. The finite direct sum is represented by its
finite product in module sheaves. The basis is prescribed, rather than chosen by the theorem.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped BigOperators

namespace WeilConjectures

section
universe cs vs rs is js

end

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : Scheme.{t})

section FreeDetection
universe ca cv cr
variable {C : Type ca} [Category.{cv} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{cr}) (T : C) (hT : IsTerminal T)
include hT

end FreeDetection

end WeilConjectures
