## What changed

Restored Sheaf.AlgebraicGeometry.FiniteEtaleTraceImage from the exact quarantine
path in coord/rework.tsv. Replaced its private import of
WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSectionDescent with
Sheaf.AlgebraicGeometry.FiniteEtaleTraceSectionDescent. The latter declares the
pro-étale finiteEtaleTrace_section_sum_descent used by traceSection and its
characterization lemmas; the former declares a different étale-site theorem.
All other source text is byte-identical to the archive. No theorem, definition,
public import, attribute, or proof body changed. No consumer adaptations.

The restored file compiled cleanly through lcompile.py in 13.7 seconds.
import_direction.py confirms the corrected import cannot form an import cycle.
LeanFinder found only ring/field trace lemmas; Loogle and Mathlib grep found no
matching sheaf trace theorem. The existing three-step proof remains the route.

Change record: coord/changes/D4-finite-etale-trace-image-import.md.

## Proved and sorry left

Assigned repair completed for AlgebraicGeometry.Scheme.finite_etale_trace_image
(node lem-sfb-finite-etale-trace-image). This is a zero-hole repair: the archived
module had 0 sorries and the restored module has 0. Holes closed: none. Holes
added: none. Split off: none. No new proof is claimed; the existing complete
proof now resolves its existing descent dependency and compiles.

## No longer needed

Removed only the direct private import
WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSectionDescent, which did not
provide the theorem used by this module. No DAG node or module is withdrawn or
claimed globally unnecessary. Retained all actual dependencies:
def-sfb-finite-etale-trace-data, lem-sfb-finite-etale-trace-section-descent and
lem-sfb-finite-etale-trace-sheet-lifting. The unit's trace-image step is preserved.

## Where the brief, the DAG or earlier work was wrong

The archived module imported the wrong root for section-sum descent after the
upstream sync. The rework row accurately identifies the unknown identifier.
The DAG already names the correct Sheaf dependency and needs no update; its
Lean attachment, statement, proof and proof_deps are preserved. There is no
return entry for this item in coord/returns/D4.md. downstream.py cannot query
the absent quarantined module, so consumer checking used direct source searches
including quarantined files. These found no Lean importers and only the
ContinuousFiniteEtaleTraceLattice docstring reference. This is not a withdrawal.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
