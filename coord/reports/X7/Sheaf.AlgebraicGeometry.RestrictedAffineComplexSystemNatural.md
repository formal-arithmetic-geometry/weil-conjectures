## What changed

Completed the listed retirement repair for
`Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural`.
`deleted.txt` withdraws that duplicate; the existing node
`lem-sbc-restricted-affine-complex-system-natural` now points to
`WeilConjectures.AlgebraicGeometry.RestrictedAffineComplexSystemNatural` and
its existing theorem
`AlgebraicGeometry.Etale.exists_restricted_affine_complex_system_natural`.
The public theorem signatures, four imports, and public proof bodies match
exactly. The source-library twin is preserved without edits.

The sole live theorem consumer,
`WeilConjectures.AlgebraicGeometry.AbelianRawCoconeComplexPresentation`, already
imports and applies that twin. All node dependencies stay; the parent keeps
using the same node through its corrected attachment. No consumer needs adapting.
The change record is
`coord/changes/restricted-affine-complex-system-natural-retirement.md`.

## Proved and sorry left

Actual item holes before: 0. Holes closed: 0. Holes added or split off: 0.
No `sorry` remains in the withdrawn item and no new theorem or definition is
introduced. The existing upstream theorem named above has a complete explicit
proof; this packet claims retirement of a duplicate, not new proof progress or
closure of its transitive dependencies.

Validation: `lcompile.py --all .../scratchpad` passed for the unchanged upstream
module (26.3 s), its unchanged direct consumer (48.5 s), and an anonymous theorem
with the exact original signature proved by applying the upstream theorem
(9.5 s). The probe's `#print axioms` reports only `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`. All three files compiled without warnings.
These verification files stay under `scratchpad/` and are not delivered.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural`.
Its duplicate declarations, private packaging helpers, and four imports leave
that module with the standard empty stub. No live or quarantined module imports
it. All four imports remain needed by the upstream implementation:
`WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology`,
`WeilConjectures.AlgebraicGeometry.HigherDirectImageRawComplexPresentation`,
`WeilConjectures.AlgebraicGeometry.RestrictedAffineNaturalCoefficientSystem`, and
`WeilConjectures.AlgebraicGeometry.RawAffineComplexSystemMapCoherence`.

No mathematical node is pruned. In particular, the coefficient-system and
map-coherence dependencies remain, as do the raw restricted-cohomology and
presentation definitions. All actual DAG parents were checked, including
quarantined source references; only
`lem-sbc-abelian-raw-cocone-complex-presentation` has a dependency edge to this
node. It is still served by the identical upstream theorem. The unit route is
preserved; zero importers alone is not the basis for withdrawal.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a holed item, but the current assignment is a
retirement repair in `coord/retire-items.tsv`; both copies currently have zero
explicit holes. The old retirement row names a Sheaf consumer that has already
been migrated to its upstream twin. Its DIFFERENT classification reflects
private helper binder names, not a difference in the public theorem, proof,
imports, or underlying definitions. The DAG attachment was the remaining stale
reference to the duplicate implementation. No new mathematical route or split
is required.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
