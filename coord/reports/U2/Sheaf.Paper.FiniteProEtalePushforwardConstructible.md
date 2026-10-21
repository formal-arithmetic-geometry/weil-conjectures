## What changed

Proved `AlgebraicGeometry.ProEtale.finite_proetale_pushforward_constructible` with
its signature and both canonical comparison definitions unchanged. Finite-type
schemes over the field are Noetherian, so the source and its diagonal give the
required qcqs hypotheses. The proved fixed-module comparison
`exceptionalTransport_constructible_comparison` supplies the input etale origin
and transports bounded constructibility back at the target. The existing
nonseparated finite-type etale direct-image theorem supplies constructibility of
the etale pushforward.

A proved private categorical helper transfers invertibility between mates for
two adjunction structures with the same functors, using conjugate isomorphisms
and `mateEquiv_whiskerTop_conjugateEquiv`. This applies the already proved
`unboundedDirectImageComparison_boundedBelow` to the exact canonical mate in
this item's conclusion. The final isomorphism is the specified mate composed
with the direct image of the chosen origin isomorphism. Explicit output bounds
are the minimum and maximum of its t-structure bounds.

Updated the existing DAG node's proof, proof dependencies, and proof origin to
record this assembly. Two existing general results from another unit are used
as tools: `new-etale-proetale-exceptional-object-comparison` is precisely the
fixed-module, arbitrary finite-ring object criterion needed here;
`lem-sfb-unbounded-direct-image-bounded-below` supplies the unbounded qcqs mate
criterion. The item's definition unit has no proof steps to bypass.

Validation: the complete item compiled through `lcompile.py` with exit code 0,
no warnings, and 13.5 seconds of compiler time. The new DAG dependencies were
checked to have no path back to this item.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.ProEtale.finite_proetale_pushforward_constructible`
(node `lem-sf-finite-proetale-pushforward-constructible`).

Holes closed: 1. Holes added: 0. Holes remaining in the item: 0.
No new modules, declarations with holes, axioms, or definition changes.

## No longer needed

Removed the direct private import
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin` and its proof dependency
`lem-weil-pbc-finite-ring-constructible-derived-origin`. Its statement uses
small-ring intrinsic modules and ULift coefficients; the existing Noetherian
fixed-module object comparison applies directly here instead.

Removed the direct private import
`Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate` and the direct proof
dependency `lem-weil-pbc-comparison-direct-image-canonical-mate`. That module and
node remain needed transitively by the bounded-below unbounded comparison;
this is not a request to withdraw them. Removed the two corresponding obsolete top-level `tool_uses` entries; the
remaining approvals keep their original order. No module is withdrawn. Existing public
imports are preserved. All other geometric proof dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The planned derived-origin input has the wrong coefficient encoding for direct
application: its ring is in Type u and its conclusion is in intrinsic ring-sheaf
modules with ULift fixed coefficients. The item instead allows arbitrary finite
B in Type (u+1) and states intrinsic constructibility in fixed ModuleCat B.
The already proved fixed-module Noetherian object comparison resolves this
without changing any statement or construction.

The planned canonical-mate input is a D+ statement, whereas the conclusion uses
the unbounded category and K-flat derived adjunctions. The already proved
bounded-below unbounded comparison plus the private conjugation calculation
resolves this. The mathematical statement needs neither separatedness nor a
finite Tor bound; neither is introduced. Empty schemes, zero objects and the
zero ring remain included, and min/max makes the chosen interval ordered.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
