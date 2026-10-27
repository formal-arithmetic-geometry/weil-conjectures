## What changed

Restored the quarantined Sheaf.AlgebraicGeometry.FiniteEtaleTraceImage module.
Replaced its private import of
WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSectionDescent with
Sheaf.AlgebraicGeometry.FiniteEtaleTraceSectionDescent. The latter declares the
existing pro-étale finiteEtaleTrace_section_sum_descent used in four places.
Every declaration, proof body, public import and signature is unchanged.
Change record: coord/changes/D2-finite-etale-trace-image-import.md.

The restored module compiles without errors or warnings through lcompile.py
(30.7 seconds). Import-direction checking accepts the corrected dependency.
Searches found no executable consumer or Lean importer to adapt. Reviewed the
existing section-descent and sheet-lifting signatures against the calls; the
three-step DAG argument and the unit's trace route remain unchanged. No node
update is required because the recorded dependencies already name these modules.

## Proved and sorry left

Assigned repair completed for AlgebraicGeometry.Scheme.finite_etale_trace_image
(lem-sfb-finite-etale-trace-image). The archived item has zero sorry holes; the
restored module has zero. Holes closed: 0 of 0. Holes added: 0. Split off: 0.
No new proof or decomposition is claimed: this restores the existing complete
proof against its actual dependency after upstream sync.

## No longer needed

Removed the private import
WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSectionDescent: its étale-site
AlgebraicGeometry.Etale.finiteEtaleTrace_section_descent is not used here and
has different coefficients and site. No DAG node or module is withdrawn.
All three existing proof dependencies remain needed: trace data, section-sum
descent and sheet lifting. The public definitions import is preserved.

LeanFinder search for the pro-étale module trace and integral sheaf image returned
algebraic étale-locus and differential results, not a replacement. Loogle query
"Sheaf", "trace" and the Mathlib grep query for the exact trace names returned
zero hits. Direct repository rg found the required existing pro-étale theorem.

## Where the brief, the DAG or earlier work was wrong

The current rework row correctly identifies the missing identifier. The archive
imports the separate upstream étale-site module instead of the existing Sheaf
pro-étale dependency. The previous D4 change record documents the same repair
before the latest sync; the current archived source again needs this correction.
The DAG dependency and attached theorem remain accurate. No statement repair,
new node, source-library edit, target change or consumer adaptation is needed.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
