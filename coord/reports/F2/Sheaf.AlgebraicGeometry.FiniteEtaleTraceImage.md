## What changed

Restored lean/Sheaf/AlgebraicGeometry/FiniteEtaleTraceImage.lean from the exact
quarantine path named by the current rework row. Retained the pro-etale descent
import, all definitions, the complete trace/image proof, its public signature,
and the existing DAG attachment and proof route. Removed redundant private
imports Mathlib.Algebra.Category.ModuleCat.Basic and
Mathlib.CategoryTheory.Category.ULift. The archived file compiles cleanly against
the current published build (29.0 seconds); the final file with both redundant
imports removed also compiles cleanly (30.3 seconds).

The proof still constructs the unique descended section, proves its naturality
and linearity, saturates the pointwise integral image using Subfunctor.sheafify,
and identifies local representatives with local sheet sums using the existing
sheet-lifting theorem. The latest blueprint's "Pushing down by the trace"
paragraph and the unit's realized trace step are retained, including empty
splittings and sheaf images rather than images on global sections.

Change record: coord/changes/F2-finite-etale-trace-image-restoration.md.

## Proved and sorry left

Repair with zero original holes: 0 holes closed, 0 holes added, 0 holes left.
AlgebraicGeometry.Scheme.finite_etale_trace_image retains its complete archived
proof (node lem-sfb-finite-etale-trace-image). All private helper proofs are
complete. No statements are split off; no theorem proof is replaced by sorry.
This restores an existing proof and is not counted as a newly closed hole.

## No longer needed

Removed the redundant private imports Mathlib.Algebra.Category.ModuleCat.Basic
and Mathlib.CategoryTheory.Category.ULift. Their facilities are already supplied
by the retained imports. No DAG node, mathematical dependency or library module
is pruned: the data, section-descent and sheet-lifting declarations are all used.

LeanFinder returned eight algebraic field/ring trace results, none stating this
pro-etale coefficient trace/image theorem; Loogle on "Sheaf", "trace" and the
Mathlib grep search returned no match. Direct library searches locate precisely
the existing pro-etale descent and sheet-lifting interfaces used in the proof.
No shorter replacement route is needed for this restoration.

## Where the brief, the DAG or earlier work was wrong

The current rework log records an unknown finiteEtaleTrace_section_sum_descent,
but the current archive already has the correct private Sheaf import and the
published build accepts its entire proof. Unlike the earlier D2/D4 repair
records, this restoration therefore does not claim to change an incorrect
WeilConjectures import in the current archive. The source-library module of the
same basename proves a different statement on the etale site and is not a
replacement for this pro-etale continuous-coefficient dependency.

The module is still needed by the DAG parent
lem-sfb-continuous-finite-etale-trace-lattice and the unit trace step. Its current
lack of Lean importers is not treated as authorization to withdraw it. No
statement, definition, source-library file, unit route or DAG record is changed.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
