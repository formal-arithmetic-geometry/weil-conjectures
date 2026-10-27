## What changed

Restored the quarantined module for the coord/rework.tsv timeout repair.
etaleLine and proLine are now ordinary semireducible definitions with explicit
original derived-category types; their bodies are unchanged. singleShiftInclusion,
extPlusMap, etaleClass, proClass, shiftedComparison, etaleTau, proTau and compactTarget
are irreducible. etaleClass and proClass apply the original Ext realization without
first unfolding the supported source. The same unique Cartier-family witness is used.
No mathematical definition, endpoint, hypothesis, class or normalization changes.
Every original declaration and the complete main theorem statement remain.
No new declarations, nodes, or split-off statements are added. The DAG's proof and
all dependencies are unchanged; its Lean attachment records the repair.

Change record: coord/changes/line-kummer-field-realization-typed-interfaces.md.

## Proved and sorry left

Assigned definition repair: 0 holes closed, 0 added, 0 split off.
One original sorry remains:
AlgebraicGeometry.LineKummerField.line_kummer_field_realization
(node lem-pur-line-kummer-field-realization), with its original source and nine-step
proof docstring. No sorry occurs in any definition or instance. No axiom is added.
The chosen data remain components of the same uniquely specified Cartier pair.
The complete repaired file compiled without errors or warnings in 42.7 seconds.
Final compilation and preflight are performed by deliver3.py.

## No longer needed

Removed these six unused private imports for the unfinished proof plan:
Sheaf.AlgebraicGeometry.VectorProjectiveCompletion,
Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine,
Sheaf.Algebra.Homology.FlatSingleDerivedNormalization,
Sheaf.AlgebraicGeometry.FiniteRootSiteComparison,
Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction,
Sheaf.CategoryTheory.ExactFunctorDerivedFunctor.
All original public imports remain. No mathematical node or module is globally
pruned: the unfinished proof may need these declared dependencies, which are all
retained in the DAG. The parent lem-pur-line-zero-class-exchange still needs this item.

## Where the brief, the DAG or earlier work was wrong

The missing source is quarantined, not withdrawn, and is restored from its recorded
archive. The original compiled once in 52.2 seconds but later runs timed out.
Low-heartbeat and profiler diagnostics identify expensive kernel checks of the
supported Ext conversions. The first generic-adapter repair also timed out during
delivery and was replaced by the smaller typed-representative repair described above.
No profiler options, heartbeat increases, linter suppression, or compiler-limit
changes are included in the packet.

Direct searches across lean/ and quarantine/ found no Lean consumer. Because the
source is quarantined, tools/downstream.py reports unknown module; DAG parent and
source searches supply the consumer check instead. No unit route changes.
No statement is disputed. No forced adaptations are needed.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
