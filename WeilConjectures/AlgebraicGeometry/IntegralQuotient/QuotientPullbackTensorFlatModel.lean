/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorNormalization
import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorLeftFlatComputation
import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorRightFlatComputation

/-! # The quotient tensor square on resolving complexes

Source: Stacks Project, Tags 07A4, 0G7E and 06YY; the representative calculation
in steps 2--5 of the quotient pullback tensor coherence argument.
(blueprint: lem-sfb-quotient-pullback-tensor-flat-model).

The statement is restricted to flat-term K-flat complexes. The parent module
performs the separate resolution and naturality argument for arbitrary inputs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

attribute [local semireducible] AlgebraicGeometry.ProEtale.QuotientChange.L

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

open QuotientChange QuotientSectionTensor

end AlgebraicGeometry.ProEtale.IntegralQuotient
