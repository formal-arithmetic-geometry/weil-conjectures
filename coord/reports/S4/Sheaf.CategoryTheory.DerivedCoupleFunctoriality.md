## What changed

Completed the listed retirement repair, rather than reproving an already proved
module. Withdrew `Sheaf.CategoryTheory.DerivedCoupleFunctoriality` via `deleted.txt`.
Its upstream twin provides the same `CoupleMorphism` and
`derivedCoupleFunctoriality` signatures over the same upstream exact couples.
Switched all five current consumers to that twin:
`Sheaf.CategoryTheory.ExactCoupleMorphism`,
`Sheaf.CategoryTheory.NaturalTruncationCouple`,
`Sheaf.Paper.ExactCoupleDifferential`,
`Sheaf.AlgebraicGeometry.TruncationExchangeAbutment`, and
`Sheaf.AlgebraicGeometry.FiniteRangeComparison`.

`FiniteRangeComparison` uses a proof-only `import all` to reuse the upstream
proved private `exactCoupleFiniteTransport` and `factors_iff_image_le` helpers.
All existing proof bodies, signatures and upstream sources are unchanged.
Repointed `lem-sp-derived-couple-functoriality` to the upstream twin, preserving
its statement, proof route and dependencies. Change record:
`coord/changes/retire-derived-couple-functoriality.md`.

Validation: all five consumers compile without warnings through `lcompile.py`
(in dependency order, with the delivered files in the overlay). Their measured
single-file times were 1.1, 2.7, 5.4, 3.5 and 3.6 seconds respectively.
`tools/downstream.py --uses` checked the structure, main theorem and helper users;
source searches checked live and quarantined imports. Upstream signatures match
the retired signatures. The attached unit has no realized statement or step
for this auxiliary node; no unit route is bypassed.

## Proved and sorry left

This is a zero-hole retirement repair: the original item had 0 sorries, and the
withdrawn item has 0. Holes closed: none (0 of 0). Holes added: none. Split-off
statements: none. No new or modified proof body, and no hollow definition.
The main theorem remains fully proved in its upstream module. The two helpers
remain fully proved there and are reused directly, rather than exposed or copied.
All adapted modules have exactly their original proof bodies and hole counts.

## No longer needed

Pruned module: `Sheaf.CategoryTheory.DerivedCoupleFunctoriality`.
Removed its import from all five current consumers, replacing each with the
upstream twin (public in `NaturalTruncationCouple`, proof-only elsewhere).
No duplicate `CoupleMorphism`, one-step construction, page iteration or main
theorem is retained. No replacement helper module is needed.
The node `lem-sp-derived-couple-functoriality` remains needed and now points at
upstream. Its existing dependencies `def-sp-exact-couple` and
`def-sp-convergence` remain used. No mathematical node or unit is pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief described a module with a hole or repair; the live
queue and `coord/retire-items.tsv` specify retirement. The original item already
has no holes. The earlier kept-copy reason referred to duplicate exact-couple
and filtration dependencies; those underlying copies have since been retired,
and the item already publicly imported upstream `ExactCoupleConvergence`.
The main upstream signatures now match. The two additional public helpers in
our copy are private upstream, so replacing every import by an ordinary import
would fail for `FiniteRangeComparison`; its proof-only `import all` resolves
that API difference without changing upstream. The older consumer list includes
an already absent `CoproductTruncationCouple`; only five live consumers remain.
The mathematical statement and proof plan were already correct.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
