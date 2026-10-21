## What changed

Restored the quarantined module `Sheaf.AlgebraicGeometry.LocalZeroBottomModelPullback`
with its existing complete proof. Replaced its public import of the withdrawn empty
`Sheaf.AlgebraicGeometry.DerivedPullback` with
`WeilConjectures.AlgebraicGeometry.DerivedPullback`, which now supplies the statement's
scheme and derived-category vocabulary. The original source fails with unknown public
identifiers `Scheme` and `HasDerivedCategory`; the repaired file compiles in 10.4 seconds.

The proof uses the existing bottom truncation arrow, local invertibility of its pulled-back
homology map, the open-cover isomorphism criterion, and the flat-single pullback comparison.
The declaration signatures, proof bodies, and existing DAG attachment and dependencies stay
unchanged. The change record is
`coord/changes/G1-local-zero-bottom-model-pullback-restoration.md`.

## Proved and sorry left

The quarantined source already had zero holes. Holes closed: none. Holes added: none.
Holes left: none. This delivery repairs and restores the module; it claims no net hole
reduction. Both `AlgebraicGeometry.Scheme.localZeroBottomModel_pullback` and the private
`flat_single_pullback_iso` have complete proof bodies. An inline `#print axioms` check for
the public theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
No new declarations or definitions are introduced.

## No longer needed

Removed the obsolete public import `Sheaf.AlgebraicGeometry.DerivedPullback`, whose live
file is an empty withdrawn module. Its mathematical dependency remains supplied by the
adopted `WeilConjectures` module. No mathematical nodes, modules, declarations, or unit
steps are pruned. All five existing proof dependencies remain needed.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole quarantine restoration, as recorded in `coord/rework.tsv` and
`coord/queue.tsv`, rather than a fresh proof obligation. The archived public import had
not followed the retirement of the duplicate derived-pullback module. Replacing that
import repairs the public statement boundary without changing the theorem.

The downstream script cannot inspect the absent live module and reports "unknown module".
A direct search of the live and quarantined source trees finds one direct importer,
the quarantined `Sheaf.AlgebraicGeometry.PerfectUniversalLowestCohomologyPullback`.
Its call to the restored theorem uses exactly the unchanged signature. Its other
quarantined dependencies are outside this restoration; it is not withdrawn or edited.
The unit `sk-prop-av-cube` and the item's existing dependency route are preserved.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
