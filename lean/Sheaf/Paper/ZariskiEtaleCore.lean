module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Functor.Flat

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- Core site data for the Zariski-to-etale inclusion.

Source: Stacks Project, Sites, Proposition Tag 00X6 and Lemma Tag 00X5;
Morphisms, Tag 02GP; Schemes, Tag 01JR.
(blueprint: lem-weil-pbc-zariski-etale-core)

Proof in words: send an open U to its open subscheme with inclusion into X,
which is etale because open immersions are etale. Send an inclusion V <= U
to the scheme inclusion over X. These are the objects and maps of
X.restrictFunctor, so forgetting the etale condition gives equality of functors;
identity and composition follow from those of restrictFunctor. A Zariski
covering family is jointly surjective on the open subscheme it covers, and its
arrows are etale, so its image generates an etale covering sieve. This proves
cover preservation, including the empty cover of the empty open.
The top open is isomorphic over X to the identity of X, hence terminal in the
etale category. Intersections V intersect W of opens over U are their scheme
fibre products: an open immersion pulls back to the inverse-image open (01JR).
The etale category is a full subcategory of schemes over X closed under these
finite limits, so the same cones are limiting there. Terminal objects and
pullbacks generate all finite limits, giving finite-limit preservation.
Cover preservation plus these pullback comparisons implies continuity: a
sheaf's gluing condition for the image covers is exactly the condition for the
original covers, as in Tag 00X6. Finally the opens have finite limits; any
finite diagram in the category of arrows T -> i(U) has a cone obtained by
taking its limit in opens and using preservation of this limit to induce the
map from T. The empty diagram uses the terminal open. Thus each such comma
category is cofiltered, which is precisely representable flatness.
This is also Mathlib's flat_of_preservesFiniteLimits criterion. -/
theorem zariski_to_etale_core (X : Scheme.{u}) :
    ∃ (i : X.Opens ⥤ X.Etale),
      (i ⋙ Scheme.Etale.forget X = X.restrictFunctor) ∧
      CoverPreserving (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology i ∧
      PreservesFiniteLimits i ∧
      Nonempty (IsTerminal (i.obj ⊤)) ∧
      ∃ (_ : i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology),
        ∃ (_ : RepresentablyFlat i), True := by
  sorry

end AlgebraicGeometry
