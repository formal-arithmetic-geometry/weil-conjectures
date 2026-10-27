## What changed

Restored Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose from the archive
specified in coord/rework.tsv. The module is byte-identical to the archive: all
seventeen declarations, public and private imports, canonical maps, mathematical
statements, and definition bodies are preserved. The module was absent from lean/;
this delivery restores its actual source, rather than withdrawing its dependency.
The existing node and its dependency edges and unit route are preserved unchanged.

The restored module compiles on the project server through lcompile.py in 11.3 seconds,
with no compiler errors or warnings. The optional local compile backend initially
reported a missing Mathlib.olean; selecting the documented server backend with
LCOMPILE_NO_LOCAL=1 gave the successful compile. No launcher tool was modified.

Change record: coord/changes/C3-finite-ring-site-tensor-transpose-restoration.md.

## Proved and sorry left

This is a quarantine restoration, with no claim of proof progress.
Holes closed: zero of one. Holes added: zero. Split off: zero.
The sole remaining hole is
AlgebraicGeometry.ProEtale.finiteRingSiteTensorTranspose
(blueprint: lem-pur-finite-ring-site-tensor-transpose).
Its original source and complete eleven-step natural-language proof are retained.
All sixteen auxiliary declarations are concrete constructions with no holes.

## No longer needed

None. No import, node, module, dependency, or unit step is pruned or withdrawn.
The archived parent Sheaf.SecSmoothPurity.FiniteGeneralRing still imports this
module, and its node det-sp-finite-general-ring still cites this result.

## Where the brief, the DAG or earlier work was wrong

The item source is quarantined, not withdrawn. The rework row records a failure
after cluster restoration, and older diagnostics include bad imports of
FiniteComparisonLocalizing, LocalizingExceptionalAdjoint and
FiniteRingEtaleCompactGenerators. Those dependencies are now available and the
entire original module compiles without a source modification. The earlier
braidedCategory elaboration issue recorded on comparison dependency nodes also
does not reproduce in the current server compile. Restoring the complete file is
the required repair of the missing library module; changing a definition merely
to make the packet differ from its archive would be unjustified.

Searches through msearch.py (Lean Finder, Loogle and Mathlib grep), the current
source-library projection-comparison lemmas, and finite comparison declarations
were read. The existing bounded projection-transport statements do not prove the
unbounded arbitrary-finite-ring theorem directly. No existing proof is replaced
by a hole, and no theorem is weakened.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
