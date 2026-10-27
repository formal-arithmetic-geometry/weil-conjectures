/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.CategoryTheory.InternalBarOrderedCupCore
public import Sheaf.CategoryTheory.InternalBarCharacterRoofCup

/-! # Agreement of the two ordered cup bracketings

Source: the ordered iteration in step 2 of the internal bar ordered-cup argument.
(blueprint: lem-sfb-internal-bar-cup-bracketing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CondensedBar CategoryTheory.CondensedDerivedRestriction
namespace CategoryTheory.CondensedBar.OrderedCup

/-- The left fold of binary graded cups equals the fixed right-associated tensor cup.
Only reassociation and unit identifications occur; the character order is preserved.
Source: ordered-cup argument, step 2, with the fixed shifted tensor convention
(blueprint: lem-sfb-internal-bar-cup-bracketing).

Proof:
The zero case is the definition of orderedCharacterCup and sourceTensor at zero,
using the zero-shift comparison. In length one, the left and right unit laws of
cupLaws identify both maps with the character class. For longer lists, apply
associativity from cupLaws repeatedly, moving parentheses without changing the
order of the factors. Naturality of the associator moves the individual class
maps through these reassociations. The canonical two-shift tensor comparison is
coherent with the tensor associator and with shift addition: this can be checked
on the shifted regular units, represented by their one-term K-flat complexes.
On their single tensor summand, both composites extract shifts in the same order
and have the same sign; localization preserves this equality. Consequently the
reassociated source comparison is sourceTensor, by its recursion. Tensor naturality
identifies the remaining product of class maps with tensorList, and the final
multiplication is orderedProduct. These equalities give the claim in every length,
including the empty list and the zero coefficient ring.
-/
theorem ordered_character_cup_eq (A : CondensedBar.Ring.{u}) (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (q : ℕ) (a : Fin q → Character A G) :
    orderedCharacterCup q a = characterCup q a := by sorry

end CategoryTheory.CondensedBar.OrderedCup
