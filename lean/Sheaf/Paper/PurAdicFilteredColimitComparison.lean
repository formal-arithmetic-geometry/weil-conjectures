/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V6
-/
module

public import Sheaf.Paper.PurAdicLineSystemData

/-! # Inverse image of filtered ring/module colimits

Source: the Rational and algebraic closure paragraph of the coefficient-twists proof
(blueprint: lem-pur-adic-filtered-colimit-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe w uC vC uD vD

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- A semilinear comparison induces a coprojection-normalized comparison of supplied
filtered colimit pairs.

Source: the rational-and-algebraic-closure paragraph of the coefficient-twists proof;
Stacks Modules on Sites, Tags 03CO and 03CY.
(blueprint: lem-pur-adic-filtered-colimit-comparison)

Proof: apply the colimit-preserving inverse image to the underlying ring and module
colimit cocones. The colimit of the component comparisons t gives their unique normalized
underlying isomorphisms. Filtered colimits commute with finite products in sheaves of sets.
Consequently a finite list of local representatives of any ring or module sections comes
from one common stage. On such representatives, the common-stage scalar formulas and
the semilinearity of t show that the isomorphisms transport ring operations and the module
action. Their equality is local, so it descends through sheafification. Transport these
operations along the ring isomorphism to obtain its algebraic inverse-image lift, and
lift the module isomorphism using the same scalar equation. The coprojection equations
are precisely the defining equations of the two colimit-induced maps. -/
theorem purAdicFilteredColimitComparison_exists
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify J CommRingCat.{w}]
    [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify K CommRingCat.{w}]
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)
    [PreservesFiniteLimits L]
    {I : Type w} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (A : PurAdicPairDiagram.{w} J I) (B : PurAdicPairDiagram.{w} K I)
    (t : PurAdicPairComparison L A B)
    (F : PurAdicFilteredColimit A) (G : PurAdicFilteredColimit B) :
    Nonempty (PurAdicColimitComparison L t F G) := by
  sorry

end CategoryTheory
