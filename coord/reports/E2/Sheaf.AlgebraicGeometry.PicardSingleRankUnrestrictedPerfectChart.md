## What changed

Shortened the complete proof of
AlgebraicGeometry.Scheme.exists_picardSingleRankUnrestrictedPerfectChart by reusing
AlgebraicGeometry.Scheme.exists_properFlatDirectImagePerfectChart. That existing theorem
has exactly the local chart, amplitude and comparison previously reconstructed in an
80-line proof block. The remaining proof transfers rank along its isomorphisms and
handles the empty-test alternative with the actual zero object, as before.

Replaced three proof imports with the existing proper-flat direct-image chart module.
All public imports, declaration signatures, definitions and docstrings are unchanged.
Updated the item's DAG proof and proof dependencies to describe this shorter route.
No source-library module is edited. The unit route is preserved.

The original current module compiled in 22.7 seconds. The shorter module compiled
cleanly in 15.6 seconds through lcompile.py (which compiled the newly restored chart
dependency in its private overlay). The final delivery also runs its declaration probe.
The archived direct consumer applies the unchanged theorem to f, E, F and s and unpacks
exactly the same fields; it needs no adaptation. Change record:
coord/changes/E2-picard-unrestricted-chart-reuse.md.

## Proved and sorry left

Zero holes before; zero holes after. Holes closed: 0. Holes added: 0. Split off: 0.
No sorry declarations remain or are added by this delivery.
The public theorem exists_picardSingleRankUnrestrictedPerfectChart and all six private
helpers remain completely proved. This is proof consolidation on a zero-hole repair
item, not a new hole closure or a decomposition.

## No longer needed

Removed these direct proof imports:

- Sheaf.AlgebraicGeometry.ProperFlatAffineCechPerfectModel
- WeilConjectures.AlgebraicGeometry.AffineFlatModuleTensorFlat
- import all Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric

The first two corresponding nodes are no longer direct proof dependencies of this
item. They, and PerfectCohomologyFromGeometric's private relative-flatness helper, remain
needed transitively by ProperFlatDirectImagePerfectChart. No mathematical module or
node becomes unreachable, so no whole-module pruning is claimed and none is withdrawn.
The existing direct-image chart node replaces the duplicated construction. The other
original dependencies remain used by the normal form and the zero-object proof.

## Where the brief, the DAG or earlier work was wrong

coord/rework.tsv lists the old quarantine/global-build repair. N2 had already restored
the complete source and corrected its obsolete derived-pullback import immediately
before E2's claim; the current source therefore has no sorry and already compiles.
This delivery makes a substantive shorter proof instead of claiming that old repair
or submitting a no-op. The DAG's affine Cech and derived-comparison steps duplicated
the existing same-unit proper-flat direct-image chart theorem; that theorem supplies
them verbatim, including arbitrary tests, rank zero and empty fibres. No statement
change, mathematical dispute, new node or unsupported witness choice is involved.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
