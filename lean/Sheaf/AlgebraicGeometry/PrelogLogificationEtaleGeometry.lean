/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PrelogLogificationData

/-!
# Change of site, geometric stalks, and characteristic quotients of logification

Source: ILO VIII, opening of §3 and §3.3.2, pp.97, 106; the arbitrary-prelog
formulation and detailed argument expand the source as in parent proof steps 4--9.
(blueprint: lem-trf-prelog-logification-etale-geometry).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Given the three logifications and their universal properties, construct the
canonical change-of-site comparison and compute the étale and characteristic stalks.
The logifications and inverse images are inputs, so this result does not assert their
existence or either logification universal property.
Source: ILO VIII, opening of §3 and §3.3.2, pp.97, 106; parent proof steps 4--9.
(blueprint: lem-trf-prelog-logification-etale-geometry).

Proof:
1. Restriction of an étale log structure to open subschemes is a Zariski log
   structure: the structural unit-locus isomorphism restricts and the functions on
   an open subscheme identify canonically with the Zariski functions there.
   The inverse-image adjunction and the assumed Zariski universal property
   identify compatible maps from F.prelog to any étale log structure with
   compatible maps from E.prelog. The assumed étale universal properties of l
   and n therefore identify maps from N and from L to every étale log structure.
   Extend their canonical prelog maps in both directions; uniqueness makes the
   composites identities. The resulting isomorphism commutes with the structural
   maps. The inverse-image Hom bijection gives a:E→F, normalized on raw sections;
   the same adjunction checks its structural equality and the final iota equation.
   These are exactly the four clauses of PrelogLogificationComparison.
2. For a pointed étale neighborhood W, send a raw section on image(W) to its
   Zariski germ at x. Conversely represent a germ on an open neighborhood V of x
   and use the pointed étale object V. Both composites are identities in the
   neighborhood colimits: W→image(W) supplies the refinement for the second one.
   Monoid sheafification preserves geometric stalks, so this yields the normalized
   eP:E_t≅P_x. Pullback of functions gives the unique ring map rho:O_x→O_t;
   its values on all open germs give IsPrelogLocalRingMap and the structural
   formula involving eP.
3. The ring map rho reflects units. A unit germ in the geometric stalk becomes
   a unit on a pointed étale neighborhood, by lifting its inverse and both inverse
   equations. Its value in the geometric residue field is nonzero, so the
   original function has nonzero value at x. Restricting to its basic open makes
   it a Zariski unit near x. Conversely every ring map preserves units.
4. Sheafification preserves the geometric stalk of the quotient presheaf. Apply
   the filtered-varying-prelog-pushout theorem to pointed étale neighborhoods.
   Using eP and step 3, the resulting pushout is precisely that for rho∘beta_x.
   Its pair formula gives eL and all germ equations of l.EtaleStalks. The value
   on [1,a] is L.unitsIn because the unit-locus structural map is bijective.
5. Form H by sheafifying the sectionwise Associates quotient of L. It is the
   universal monoid sheaf receiving a map from L that kills every monoid unit,
   hence supplies h. In filtered stalks, unit germs and equality witnesses lift
   to one neighborhood. Thus this quotient has stalk Associates(L_t), before and
   after sheafification. Compose with step 4 to get h.EtaleStalks, with exactly
   its pair formula. That formula holds for every normalized rho and eP: they
   are uniquely determined on the raw germs, which generate the relevant stalks.
6. Slice sheafification commutes with the slice-forgetful functor, which is
   continuous and cocontinuous. Both quotient constructions and all their pair,
   structural, inclusion, and quotient maps restrict sectionwise. The comparison
   fixes the sheafification unit. This gives l.Restricts, n.Restricts and h.Restricts.

This argument uses arbitrary commutative monoids. Unit lifting uses finite inverse
equations, not cancellation or injective transition maps; the empty scheme is allowed. -/
theorem prelog_logification_etale_geometry (X : Scheme.{u}) [IsLocallyNoetherian X]
    (P : ZariskiPrelogStructure X) (Z : ZariskiLogStructure X)
    (z : PrelogPushoutPresentation (Opens.grothendieckTopology X.carrier)
      P.monoidSheaf.obj X.presheaf P.alpha Z.monoidSheaf Z.alpha)
    (hz : z.ZariskiUniversal P Z)
    (E : PrelogEtaleInverseImage P)
    (L : EtaleLogStructure X)
    (l : PrelogPushoutPresentation X.smallEtaleTopology E.prelog.monoidSheaf.obj
      X.etaleStructurePresheaf E.prelog.alpha L.monoidSheaf L.alpha)
    (hl : l.EtaleUniversal E.prelog L)
    (F : PrelogEtaleInverseImage Z.toZariskiPrelogStructure)
    (N : EtaleLogStructure X)
    (n : PrelogPushoutPresentation X.smallEtaleTopology F.prelog.monoidSheaf.obj
      X.etaleStructurePresheaf F.prelog.alpha N.monoidSheaf N.alpha)
    (hn : n.EtaleUniversal F.prelog N) :
    ∃ (H : Sheaf X.smallEtaleTopology CommMonCat.{u})
      (h : PrelogCharacteristicPresentation X.smallEtaleTopology L.monoidSheaf H),
      PrelogLogificationComparison P Z z E F L N l n ∧ l.EtaleStalks P E L ∧
      h.EtaleStalks P E L H l ∧ l.Restricts ∧ n.Restricts ∧ h.Restricts := by sorry

end AlgebraicGeometry
