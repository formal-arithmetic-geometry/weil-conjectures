## What changed

Proved `AlgebraicGeometry.Etale.closedSupport_openCounit` in
`Sheaf.AlgebraicGeometry.ClosedSupportOpenCounit`, preserving its statement and the
definitional values of its two public definitions. Private proved helpers construct the canonical
pullback isomorphism and its naturality, the sectionwise restriction comparison,
vanishing away from the support, sheaf counit invertibility on geometric stalks,
and invertibility of its specified derived localization. A general exact-adjunction
lemma combines the standard degree-zero comparison with this counit result. The last equation is
counit naturality for arbitrary morphisms in the unbounded derived category.

The pullback and restriction constructions have private irreducibility attributes
and explicit projection lemmas to avoid unfolding their large constructions during
subsequent proof checking. Updated the existing node's proof to name the actual
vanishing lemma used. The two public arrow definitions now specialize generic constructors for arbitrary
exact functors, avoiding repeated kernel endpoint checks. Expanding those constructors
gives the original bodies. No statements were changed. The construction is recorded in
`coord/changes/G3-closed-support-open-counit-composites.md`; the consumer scan found
no other uses to adapt.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Etale.closedSupport_openCounit`
(node `lem-pur-closed-support-open-counit`). Added 0 holes. No `sorry` remains
in the delivered module, and no new modules or nodes are introduced.

The argument covers empty schemes, zero coefficients and zero sheaves without
nonemptiness assumptions. Outside the open, closedness of the composite is used
to produce an actual open neighbourhood disjoint from its support. The localization
uses the original termwise counit, not an arbitrary adjunction on the same functors.

## No longer needed

Removed proof imports:

- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`: its theorem is
  unnecessary for the categorical `ModuleCat A`-valued inverse image along an open
  immersion; the existing exactness instances already supply the derived functors.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: the published geometric-fibre API and
  conservativity theorem suffice, so the separate pointed-colimit construction
  (`def-weil-pbc-geometric-stalks`) is not used in the proof.

The proof does not require `prop-weil-pbc-inverse-image-modules-exact` as a proof
lemma; its statement-level edge remains, since it belongs to the original node's
mathematical setup. Other branches may still need both removed imports, so no
library module is withdrawn. No other declared dependencies are pruned.

## Where the brief, the DAG or earlier work was wrong

The proof plan is valid. Its explicit cofinal-neighbourhood argument inside the open
is already packaged by the library's invertible open-adjunction unit and the fibre
comparison. For vanishing outside the support, use the existing proved
`lemma-openclosed-vanishing-lowerstar` as a tool; it has the same statement for the
module coefficient category and needs no new lemma. The unit route is unchanged.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
