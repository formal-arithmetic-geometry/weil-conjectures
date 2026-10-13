/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Descent of compatible immersions

Source: Stacks Project, Tags 01JB and 01JC; Tag 0BDL, gluing characterized patches.
(blueprint: lem-sc-compatible-immersion-gluing).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Compatible immersions over a point-indexed open cover descend to Cartesian charts.
Source: Stacks Project, Tags 01JB and 01JC, applied to the characterized patches
in the final paragraph of Tag 0BDL.
(blueprint: lem-sc-compatible-immersion-gluing).

Proof:
1. Put q i = j i followed by the inclusion of U i in S. Restrict W i to
   V(i,k) = the inverse image of U k under q i. Its map to S factors both through
   U i and through U k. Compatibility with i,k gives a factor of the latter map
   through j k, hence a map V(i,k) to W k over S. Its image lies in V(k,i), so it
   factors through that open restriction. Reversing i,k gives the inverse: after
   composition into S each composite is the original structure map, and q i and
   q k are monomorphisms. The same cancellation proves uniqueness.
2. These unique isomorphisms restrict to the triple intersections and satisfy
   the cocycle identity, because both composites have the same map to S. The
   restriction maps V(i,k) to W i are open immersions. Apply scheme gluing
   (Tags 01JB and 01JC) to obtain Z with open charts e i from W i. The maps q i
   agree on the overlaps, so open-cover morphism gluing gives a map q from Z to S.
3. The image of e i is the inverse image of U i under q. One inclusion follows
   from q composed with e i = q i. For the other, choose a chart e k containing
   a point z whose image under q lies in U i. Its preimage in W k belongs to
   V(k,i), whose comparison with V(i,k) identifies z with a point in the e i
   chart. Thus the two open subsets coincide. Since e i and the inclusion of U i
   are open immersions, this equality and the commutative square give the
   asserted Cartesian square (the universal property of an open restriction).
   For empty S the point-indexed family is empty; take the empty scheme for Z
   and its unique map to S, and the chart assertions are vacuous. -/
theorem exists_gluedCompatibleImmersionCharts (S : Scheme.{u})
    (U : S → S.Opens) (hU : ∀ s : S, s ∈ U s)
    (W : S → Scheme.{u}) (j : ∀ s : S, W s ⟶ (U s).toScheme)
    (hj : ∀ s : S, IsImmersion (j s))
    (hcompat : ∀ (i k : S) {T : Scheme.{u}}
      (a : T ⟶ (U i).toScheme) (b : T ⟶ (U k).toScheme),
      a ≫ (U i).ι = b ≫ (U k).ι →
      ((∃ h : T ⟶ W i, h ≫ j i = a) ↔ (∃ h : T ⟶ W k, h ≫ j k = b))) :
    ∃ (Z : Scheme.{u}) (q : Z ⟶ S),
      ∀ i : S, ∃ e : W i ⟶ Z, IsPullback (j i) e (U i).ι q := by sorry

end AlgebraicGeometry.Scheme
