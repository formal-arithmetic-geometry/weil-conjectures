## What changed

Proved the body of `AlgebraicGeometry.Etale.sfP1CoordinateIntegrals` from the existing
arbitrary-base ordinary integral theorem and one new map-comparison theorem.
The original signature, public imports, and all existing definitions are unchanged.

The coordinate isomorphism is constructed in Lean: rename homogeneous polynomials,
check the irrelevant ideals, use `Proj.map` in both directions, and base-change by
`pullback.map`. The explicit index equivalence and projection equation are proved. The private
coordinate-isomorphism constructor is irreducible, so subsequent derived-category
proofs do not expand its underlying `Proj` maps unnecessarily.
The lisse rank-one assertion is proved from the existing finite twist theorem by
transporting its slice trivializations to actual inverse images. The coefficient
isomorphism is the inverse existing normalized shifted-line comparison.

The new module `Sheaf.AlgebraicGeometry.SfP1IntegralTransport` isolates comparison
of ordinary and compact-support composites. Its constant-object comparison is passed as an
isomorphism with explicit endpoints. This avoids expanding specialized derived
monoidal-unit definitions when a consumer only needs inverse identities. Its statement applies to arbitrary
supported Ext representatives and never asserts that an integral is identity.
The parent applies the two existing ordinary identity equations, functoriality,
and cancellation of the constant-object comparison to finish both integrals.
Validation: the final assigned module compiled successfully in 20.9 seconds;
the new comparison module also compiled successfully (53.2 seconds).
Cancellation is proved once in arbitrary categories. The module-local derived-category
instance witnesses match those captured by `DerivedCategoryModule`, as in the
neighboring supported-Kummer modules; they do not register public instances.

## Proved and sorry left

Original holes: 1. Closed: `AlgebraicGeometry.Etale.sfP1CoordinateIntegrals`
(node `lem-sf-p1-coordinate-integrals`). No sorry remains in the assigned module.

Added holes: 1. `AlgebraicGeometry.Etale.sfP1IntegralTransport`
(node `lem-sf-p1-integral-transport`) is the sole sorry in the new module.
Its complete proof in words is in the docstring and its node.

This is a decomposition, not a net hole reduction: 1 closed minus 1 added is 0.
The coordinate-renaming construction, lisse assertion, coefficient comparison,
and use of both existing ordinary integral identities are proved Lean glue.

## No longer needed

Removed the assigned module's direct proof import of
`Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: it uses the existing normalized
`OrdinaryFiniteTwistTransport` and `ordinaryFiniteShiftedLinePullback` instead.
The pullback module remains a transitive dependency; no withdrawal is proposed.

The parent no longer directly needs `lem-asd-ordinary-supported-kummer`: the
supported witness is already supplied by `finiteP1DiagonalProperty` in the
existing arbitrary-base theorem. That node remains needed by the existing
ordinary theorem; it is not globally pruned.

`lem-asd-etale-finite-twist-pullback`,
`lem-kun-proper-base-change-torsion-ring`, and
`lem-sfb-ringed-derived-monoidal-comparisons` are now dependencies of the isolated
map-comparison step instead of direct proof steps of the parent. Their modules
remain needed. No modules or nodes are claimed to leave the targets' closure.
The unit route and every source-library declaration are preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan describes the ordinary-to-compact-support and coordinate
comparison in prose but its recorded dependencies do not expose that comparison
as a Lean declaration. Generic proper exchange alone does not identify the
specific chart traces, section maps and coefficient comparisons used here.
The new node isolates precisely those map equalities. In particular it has no
hypothesis repackaging the desired integral identities, no Kummer-normalization
hypothesis on its Ext representative, and no identity conclusion. It is not the
original existence-and-integrals theorem under another name.

The existing finite twist theorem gives trivializations on localized sites;
`IsLisseRankOneSheaf` asks for inverse-image trivializations. Their comparison is
proved explicitly, rather than treating the two formulations as definitionally equal.

## New nodes

`lem-sf-p1-integral-transport`, in
`dag/nodes/sec-six-functors-basics/lem-sf-p1-integral-transport.json`, records the
comparison for an arbitrary proper morphism isomorphic over its base to the
standard projective line, an arbitrary normalized splitting family satisfying
its existing base-change equation, and any supported Ext representative.
Its source is the canonical-exchange comparison preceding the two triangle
computations in the current blueprint. LeanSearch, LeanFinder, Loogle and local
searches found no theorem supplying it. Polynomial renaming found by search is
used in the proved parent helper instead of left as a new obligation.

The edge cases were checked mathematically: the comparison is linear in the
Ext representative (including zero); it preserves identity composites by
functoriality; the argument needs no nonempty-base or nonzero-ring assumption.
It also makes no Noetherian or boundedness assumption. The parent still gets its
ordinary supported Kummer representative and positive N hypothesis from the
unchanged existing theorem.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
