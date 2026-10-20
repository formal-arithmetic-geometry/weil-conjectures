## What changed

Completed the listed retirement repair for
Sheaf.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullback. The module is withdrawn
through deleted.txt and its node points at the fully proved upstream twin. Moved its
proved private presheaf-equality bridge to the only direct consumer,
Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictHomData, switched that consumer's
proof import to WeilConjectures.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullback,
and rewrote the upstream isomorphism through the equality before the existing
sheafification argument. The consumer's public signature and public imports are unchanged.
Updated both affected node proofs to describe the actual route. No upstream file is edited.

The bridge uses uniqueness of exterior-power restrictions on pure wedges, including
n = 0. Its proof requires neither nonempty opens nor a nonempty scheme, and the
upstream comparison is quantified over all degrees and opens. The unit route is kept.

Validation: the adapted ExteriorSheafRestrictHomData and its unchanged direct importer
ExteriorSheafRestrictIso compile individually through lcompile.py. The latter was
checked against the sandbox overlay and is not included as an unchanged delivery file.

Change record: coord/changes/retire-exterior-presheaf-open-pullback-b3.md.

## Proved and sorry left

This is a zero-hole retirement repair. The current shared item already has zero
sorries after H6's component-data retirement adaptation. Closed: none (0 of 0).
Added: none. Split off: none. No sorry remains in any delivered module.

The private exteriorSheafPresheaf_eq_exteriorPower is preserved with its complete proof,
and exteriorSheaf_restrict_hom_data is proved through the upstream presheaf comparison.
The mathematical result exteriorPresheaf_open_pullback remains fully proved upstream,
attached to lem-sc-exterior-presheaf-open-pullback. The component-data theorem remains
needed and is not pruned.

## No longer needed

Retired module: Sheaf.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullback.
Removed its private import from ExteriorSheafRestrictHomData and replaced it with the
upstream twin. The retired module's imports no longer appear in that withdrawn file;
the consumer continues to need ExteriorSheaf and the upstream theorem continues to
need ExteriorPresheafOpenPullbackData. No mathematical DAG node is withdrawn.
Both node attachments and all parent dependencies are preserved, with the item node
now attached upstream. No additional module or dependency is claimed to be pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief mentions remaining holes, but the current item is the listed
retirement repair in coord/retire-items.tsv. H6's recent data-module retirement had
already proved this item and introduced the private equality bridge. Merely recompiling
that file would not complete the assigned retirement. This delivery removes the copy
and migrates its consumer, while preserving the old exteriorSheaf API at that consumer.
No false statement or unit-route error was found.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
