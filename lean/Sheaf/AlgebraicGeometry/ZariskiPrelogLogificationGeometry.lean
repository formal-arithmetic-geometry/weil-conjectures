/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PrelogLogificationData

/-!
# The Zariski part of the prelog logification construction

Source: ILO VIII, opening of §3 and §3.3.2, pp.97, 106; the arbitrary-prelog
formulation and the detailed argument are the agent-written expansion of that source
in steps 2, 3, 6, 8, 9 of lem-trf-zariski-prelog-logification-comparison.
(blueprint: lem-trf-zariski-prelog-logification-geometry).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Construct Zariski logification and its characteristic quotient, with their
normalized stalks and slice restrictions. This assertion involves only the Zariski
site; it neither constructs an étale inverse image nor asserts a change-of-site comparison.
Source: ILO VIII, opening of §3 and §3.3.2, pp.97, 106; parent proof steps 2, 3, 6, 8, 9.
(blueprint: lem-trf-zariski-prelog-logification-geometry).

Proof:
1. Form on each open U the specified congruence quotient of P(U) × O(U)ˣ.
   Restrictions carry generators to generators, hence give a presheaf Q. Its map
   [p,a] ↦ beta(p)a is natural. Sheafify Q in commutative monoids and extend this
   map to the structure sheaf. The quotient map followed by the sheafification
   unit defines z.pairMap, and p ↦ [p,1] defines z.iota. The sheafification Hom
   bijection gives z.universal on natural pair maps, because every class has a pair
   representative.
2. A section of the sheafification is locally represented by [p,a]. If its
   structural image is a unit, beta(p) is a unit on the same neighborhood, and
   [p,a]=[1,beta(p)a]. These equalities glue. The structural map on [1,a] is a,
   proving both uniqueness and existence of the inverse unit map, also on stalks.
   Thus the constructed prelog sheaf is a Zariski log structure Z.
3. For a compatible map f:P→K to a log structure, use the inverse unit map j_K
   and descend [p,a] ↦ f(p)j_K(a). It respects each generator since f(e) is the
   unique lift of beta(e) when beta(e) is a unit. It extends uniquely by
   sheafification. Its structural equality is checked on pairs. Every structural
   map fixes j_K, so agreement on the inclusion of P implies agreement on pairs
   and hence everywhere. This is z.ZariskiUniversal.
4. On the filtered system of open neighborhoods of x, sheafification preserves
   stalks: a local representative lifts a germ, and equality of germs is witnessed
   after shrinking. The filtered-varying-prelog-pushout theorem identifies the
   quotient stalk with the pushout of P_x and O_xˣ. Its formula on pair
   representatives gives the first normalization of z.ZariskiStalks. The second
   follows since the structural inverse image of each unit is unique.
5. Quotient Z(U) by its monoid units and sheafify. Maps killing units factor
   uniquely through this quotient and then through its sheafification, giving K
   and k. A unit germ lifts to a unit on a neighborhood (lift the inverse and
   shrink to enforce the two inverse equations). Likewise each equality witnessing
   association lifts after shrinking. Thus quotienting by units commutes with
   these filtered stalks. Combine this with step 4 to obtain the stated Associates
   stalk and its formula on pairs, exactly k.ZariskiStalks.
6. Restriction to the slice over an open commutes with sheafification by the
   continuous and cocontinuous slice-forgetful functor. The comparison fixes the
   sheafification unit. Quotients, pairs, and their maps restrict sectionwise, so
   the restricted presentations have exactly the displayed pair and quotient maps.
   This gives z.Restricts and k.Restricts.

No integrality, finite generation, or nonemptiness is used: on the empty scheme
all stalk clauses are vacuous, and the sheafification constructions still apply. -/
theorem zariski_prelog_logification_geometry (X : Scheme.{u}) [IsLocallyNoetherian X]
    (P : ZariskiPrelogStructure X) :
    ∃ (Z : ZariskiLogStructure X)
      (z : PrelogPushoutPresentation (Opens.grothendieckTopology X.carrier)
        P.monoidSheaf.obj X.presheaf P.alpha Z.monoidSheaf Z.alpha)
      (K : TopCat.Sheaf CommMonCat.{u} X.carrier)
      (k : PrelogCharacteristicPresentation (Opens.grothendieckTopology X.carrier)
        Z.monoidSheaf K),
      z.ZariskiUniversal P Z ∧ z.ZariskiStalks P Z ∧ k.ZariskiStalks P Z K z ∧
      z.Restricts ∧ k.Restricts := by sorry

end AlgebraicGeometry
