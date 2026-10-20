## What changed

Retired the duplicate module
Sheaf.AlgebraicGeometry.FinitePresentationOverlapChartEquations listed in
coord/retire-items.tsv. Its existing upstream twin proves the same result without
the unused Noetherian hypothesis. The complete old signature specializes directly
from upstream; the scratch specialization compiled and printed exactly propext,
Classical.choice, and Quot.sound. Both theorem proof bodies are identical.

Changed only the private chart-equations import in
Sheaf.AlgebraicGeometry.FinitePresentationOverlapCoherence, which compiled cleanly
through lcompile.py. Reattached lem-pc-fp-overlap-eventual-chart-equations to the
upstream theorem and recorded its signature verbatim. The mathematical statement,
proof steps, proof dependencies, parent dependency edges, and unit route are kept.
The existing upstream source is unchanged.

Change record: coord/changes/T2-retire-fp-overlap-chart-equations.md.

## Proved and sorry left

The assigned retirement starts with zero local holes and ends with zero. Holes
closed: 0 of 0. Holes added: 0. Split off: 0. No sorry remains in any delivered
Lean file. AlgebraicGeometry.exists_finitePresentation_overlap_eventual_chart_equations
is supplied by its already-proved upstream declaration. The scratch theorem of
the exact old signature is only verification and is not delivered.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.FinitePresentationOverlapChartEquations.
Removed its private import from FinitePresentationOverlapCoherence and replaced it
with WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapChartEquations.
The duplicate's private pullback constructions are unnecessary copies of the same
upstream constructions. No mathematical node or upstream proof dependency is
pruned: the chart-equations node remains needed by the coherence parent and its
proof still uses the diagonal-eventually and triple-eventually nodes and local
overlap transitions. No new nodes or modules are introduced.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief mentions an obligation split off four times, but the
current queue explicitly assigns duplicate retirement and the assigned module has
no sorry. Its node still pointed to the Sheaf duplicate, even though upstream
already provides the result with the same conclusion and one fewer hypothesis.
The replacement is therefore retirement and attachment reconciliation, not a new
decomposition. The full signature comparison, source searches, exact-signature
specialization, and consumer compile verify the replacement. Empty covers and
directed preorders are handled by the identical upstream proof, which includes k
in the finite set of stages before taking an upper bound.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
