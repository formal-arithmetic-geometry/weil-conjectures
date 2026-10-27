## What changed

Replaced the proof of `AlgebraicGeometry.Etale.etaleGraphShrinkFirstLeg` without changing
its statement. The proof first establishes composition of the proper/open triangles,
then combines its inverse with associativity of derived open extension. It specializes
this calculation to the intersection inclusion and the first projection, and transports
along the unchanged first graph lift. All added helpers are private and proved.

Proof imports: `EtaleRefinementGraphMiddleTransport` (its proved generic
`concrete_triangle_transport` helper) and `UnboundedEtaleCompactSupportComparisons`
(the comparison of the formalism's open compositor with the specified derived compositor).
The existing public import is preserved. The generic `first_leg_pasting` helper
handles equality of the first graph lifts before specialization to the dependent
pullback expressions.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.etaleGraphShrinkFirstLeg`
(`lem-pur-etale-graph-shrink-first-leg`), the module's one original hole.
Added holes: none. Sorries left: none. No new axioms or postponed data constructions.

Validation: `lcompile.py` compiled the complete module without warnings or errors
in 11.4 seconds, below the 60-second limit.

## No longer needed

No existing imports removed and no modules withdrawn. The proof avoids a new direct
application of the existential `etaleProperOpenExchangeCube`, using the already proved
Cartesian triangle transport instead. That cube is still a transitive import of the
transport module, so this is not a claim that its module leaves the target closure.
The second projection, second-neighborhood triangle, and full middle comparison are unused.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair. The generic comparison lemmas are tools for
the same prescribed pasting calculation; no unit route is replaced.
The planned normalized-pasting argument works;
the existing generic transport helper supplies its triangle subcalculation. Empty opens
and identity inclusions require no additional cases: the proof uses naturality,
invertible comparison maps, and universal projection equations only.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
