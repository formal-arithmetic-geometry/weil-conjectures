/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import all WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Algebra.Homology.BifunctorSingleNaturality

/-! # Tensor associativity for the internal integral reduction tower

Source: blueprint latest, det-lem-int-tensor-product.proof.md, first paragraph.
(blueprint: lem-sfb-tensor-integral-reduction-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale.AdicCompletion

attribute [local irreducible] upperStarFromPoint

end AlgebraicGeometry.ProEtale.AdicCompletion
