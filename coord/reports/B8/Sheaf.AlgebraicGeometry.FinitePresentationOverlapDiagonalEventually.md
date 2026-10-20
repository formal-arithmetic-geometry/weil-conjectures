## What changed

Retired the duplicate module
Sheaf.AlgebraicGeometry.FinitePresentationOverlapDiagonalEventually, as listed in
coord/retire-items.tsv. Its only direct importer,
Sheaf.AlgebraicGeometry.FinitePresentationOverlapChartEquations, now imports
WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapDiagonalEventually
privately. Its proof and signatures are unchanged. The adapted consumer compiled cleanly
through lcompile.py in 10.4 seconds. Updated the existing node's
Lean attachment to the upstream declaration. No upstream source is changed.

Change record: coord/changes/retire-fp-overlap-diagonal-eventually-B8.md.

## Proved and sorry left

The assigned module started with zero sorries. Closed: none (0 of 0).
Added: none. Split off: none. No sorry remains in the withdrawn module or in
the adapted consumer. This is duplicate retirement, not a new proof.
The existing upstream finitePresentation_overlap_diagonal_eventually proves the
required result with no Noetherian hypothesis; all other binders and the entire
conclusion match exactly. Its identity-defect proof is preserved.

## No longer needed

The Sheaf.AlgebraicGeometry.FinitePresentationOverlapDiagonalEventually module
and its private import by FinitePresentationOverlapChartEquations are retired.
The existing node lem-pc-fp-overlap-diagonal-eventually remains needed and now
attaches upstream. The proof dependencies def-pc-local-overlap-transitions,
pqf-def-coherent, and lem-pc-fp-chart-map-zero-eventually remain needed by the
upstream argument; none is claimed pruned. All public imports remain available
through the consumer's existing imports or the replacement upstream proof import.
No other module or node is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes this item as containing a hole, but the
current module is already proved and listed for retirement. The stale node
attachment points to its redundant Sheaf twin. The adopted upstream theorem is
strictly more general only in omitting the Noetherian instance; specializing it
requires no argument beyond the consumer's unchanged application. Both proofs
use the same identity defect and canonical chart-map persistence, so the unit's
route is preserved (its realized lists are empty).

Searches actually run: LeanFinder returned pullback/gluing identity lemmas but no
eventual overlap theorem; Loogle did not know the project declaration; msearch
grep returned zero hits. Direct rg on both library roots found the exact
upstream theorem and the sole direct consumer. No new statement is introduced.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
