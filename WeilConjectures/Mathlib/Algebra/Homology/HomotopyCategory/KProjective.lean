/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Biproducts of K-projective cochain complexes

The binary biproduct of two K-projective cochain complexes is K-projective.
This is the dual of the corresponding statement for K-injective complexes in
`WeilConjectures/FromJoel/Algebra/Homology/HomotopyCategory/KInjective.lean`.

In mathlib, this file would be
`Mathlib/Algebra/Homology/HomotopyCategory/KProjective.lean`.

-/

@[expose] public section

namespace CochainComplex

open CategoryTheory Limits

variable {C : Type*} [Category C] [Abelian C]

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts in
instance (K L : CochainComplex C ℤ) [hK : K.IsKProjective] [hL : L.IsKProjective] :
    (K ⊞ L).IsKProjective := by
  rw [isKProjective_iff_leftOrthogonal] at hK hL ⊢
  refine ObjectProperty.prop_of_iso _
    ((HomotopyCategory.quotient C (.up ℤ)).mapBiprod K L).symm ?_
  apply ObjectProperty.prop_biprod_of_isClosedUnderBinaryProducts
  all_goals assumption

end CochainComplex
