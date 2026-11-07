/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Submission.WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.FiniteProducts

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# K-injective cochain complexes

Supplement to `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

namespace CochainComplex

open CategoryTheory Limits

variable {C : Type*} [Category C] [Abelian C]

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts in
instance (K L : CochainComplex C ℤ) [hK : K.IsKInjective] [hL : L.IsKInjective] :
    (K ⊞ L).IsKInjective := by
  let S := (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
  rw [isKInjective_iff_rightOrthogonal] at hK hL ⊢
  refine ObjectProperty.prop_of_iso _
    ((HomotopyCategory.quotient C (.up ℤ)).mapBiprod K L).symm ?_
  apply ObjectProperty.prop_biprod_of_isClosedUnderBinaryProducts
  all_goals assumption

end CochainComplex
