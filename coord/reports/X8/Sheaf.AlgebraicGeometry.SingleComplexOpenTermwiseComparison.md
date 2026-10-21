## What changed

Restored the quarantined Sheaf.AlgebraicGeometry.SingleComplexOpenTermwiseComparison as a
public re-export of WeilConjectures.AlgebraicGeometry.SingleComplexOpenTermwiseComparison.
The adopted source already proves AlgebraicGeometry.exists_singleComplexOpen_termwise_comparison
by the complete planned argument: restrict K-flatness, invert the pinned counit, use the ordinary
comparison and counit-compatibility squares, then cancel the original counit. The historical
module now uses that unique implementation instead of redeclaring the theorem and depending on
withdrawn or duplicated Sheaf proof helpers. All four original public imports are retained.
No file of the adopted source tree or the quarantine archive is changed.

Updated the item's node lean record to existing=true with an explanation of the re-export.
Its module/file attachment, mathematical statement, proof steps and dependency edges remain.
The source's IsKFlatTensor and the historical IsAcyclicTensorKFlat have identical defining
acyclic-tensor formulas. A private scratch probe checks the entire archived theorem signature
by directly applying the adopted theorem, including both input and output K-flatness predicates.
The canonical representative, localization factor, counit, additive stalk isomorphism and square
are all unchanged. This handles empty opens, top opens, zero complexes and zero rings with no
extra hypotheses.

Change record: coord/changes/X8-termwise-comparison-upstream-reexport.md.
The independent maintainer reader reviews this zero-hole environment repair.

## Proved and sorry left

The quarantined item has zero sorry bodies; the restored module also has zero.
AlgebraicGeometry.exists_singleComplexOpen_termwise_comparison is provided by the already proved
adopted source declaration. Holes closed: 0. Holes added: 0. Split off: 0.
No declaration is left with sorry by this delivery; this is an assigned restoration/interface
repair, not a claim of new proof progress.

## No longer needed

The restored wrapper no longer needs these archived private proof imports:
Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel,
Sheaf.AlgebraicGeometry.IsomorphismPullbackCounit,
WeilConjectures.AlgebraicGeometry.SingleComplexOpenOrdinaryComparison, and
WeilConjectures.AlgebraicGeometry.SingleComplexOpenTermwiseCounitCompatibility.
The source proof imports its own restriction and counit helpers and still uses ordinary comparison
and counit compatibility; those mathematical nodes are not pruned.
The duplicate private comparison_square_cancel and duplicate public theorem body are no longer
needed in the wrapper. The actual proof remains intact in the adopted source.
No mathematical node or module is withdrawn, and no unit route is bypassed.
In particular the DAG parent lem-pc-single-complex-open-normalized-transport remains needed;
its quarantined module Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateStalkTransportData
still imports this historical path and applies the same theorem.

## Where the brief, the DAG or earlier work was wrong

This assignment is a quarantined zero-hole repair, not a theorem with an unfilled sorry.
coord/rework.tsv preserves the archive and its attachment; absence from lean/ is not withdrawal.
The old global failure in coord/returns/V4.md concerns a duplicate stalk-comparison declaration.
That dependency has since become a public source re-export. This delivery does the corresponding
repair for the termwise theorem instead of restoring a second declaration of the upstream name.
Compiling the unmodified archive reproduces `Unknown identifier counit_isIso_kFlat` at line 142
(7.7 seconds). Its Sheaf.AlgebraicGeometry.IsomorphismPullbackCounit import is now an empty
module; the actual helper is in WeilConjectures.AlgebraicGeometry.IsomorphismPullbackCounit.
The downstream tool with --allow-missing reports no live importers; the quarantine and DAG search
find the parent above, which is explicitly preserved. No claim is based on zero live importers.

Searches run: LeanFinder for the K-flat derived-pullback counit, Loogle for left-derived
isomorphism API (query rejected by the service), Mathlib grep for counit_isIso/isIso_counit,
and repository rg for counit_isIso_kFlat and exists_singleComplexOpen_termwise_comparison.
The repository search finds the exact complete adopted proof; no new intermediate result is needed.
The first compile request returned server-busy code 124; the restored wrapper subsequently compiled
in 2.7 seconds. Server queue time is distinct from Lean compilation time.

Validation completed with lcompile.py in import order: restored wrapper 2.4 seconds;
unmodified quarantined parent 42.9 seconds; full archived-signature application probe 6.2 seconds.
The first two compiled without warnings. The scratch-only signature probe emitted style warnings
for its global heartbeat option and exclusively private declaration, with no errors; it is not
delivered. #print axioms on the re-exported theorem reports exactly propext, Classical.choice,
and Quot.sound, with no sorry axiom. Both temporary check modules were removed from lean/ before
delivery; the parent's original source remains unchanged and quarantined.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
