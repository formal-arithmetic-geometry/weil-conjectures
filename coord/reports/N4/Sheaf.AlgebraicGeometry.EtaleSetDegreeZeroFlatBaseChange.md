## What changed

Restored `lean/Sheaf/AlgebraicGeometry/EtaleSetDegreeZeroFlatBaseChange.lean`
from its archive listed in `coord/rework.tsv`. Adapted the chart-cover destructuring
in `AlgebraicGeometry.isIso_etaleSetDegreeZeroBaseChange_of_flat` to the current
`AlgebraicGeometry.exists_etaleCover_factorization`: retain its trailing conclusions
as `hrest` and extract the precisely typed factorization equation `hfac` by `tauto`.
This handles the additional chart properties without depending on their number.
The actual factorization equation is then available at the pullback construction.

Both public theorem signatures, all imports, definitions, attributes, and the rest
of the archived proofs are unchanged. This is a repair of an already proved module,
not a new proof or a decomposition. The existing node
`sbc-lem-degree-zero-flat-base-change` still records the implemented chart argument;
its Lean attachment and all dependencies are preserved, so no node edit is needed.

Consumer check: `tools/downstream.py --allow-missing --uses` reports no current live
importers because the module is quarantined. A search of both `lean/` and
`quarantine/` finds the archived `Sheaf.AlgebraicGeometry.AbelianDegreeZeroFlatBaseChange`
as its direct importer and caller. Its application
`isIso_etaleSetDegreeZeroBaseChange_of_flat sq hf ((U T).obj F)` still has exactly
the same signature. No consumer adaptation is required.

## Proved and sorry left

The archived and repaired module both contain zero `sorry`s. Holes closed: zero.
Holes added or split off: zero. No `sorry` remains in either
`AlgebraicGeometry.isIso_etaleSetDegreeZeroBaseChange_of_flat` or
`AlgebraicGeometry.isIso_etaleSetDegreeZeroBaseChange_of_smooth`, nor in any helper.
The assigned compile repair preserves these existing proofs. The restored module
compiled successfully through `lcompile.py` in 24.0 seconds, with exit code zero
and no diagnostics. The delivery preflight checks its declarations and axioms.

## No longer needed

None. No imports, declarations, modules, nodes, or dependency edges are pruned.
The chart's new affineness and section conclusions are unnecessary for this proof;
only their accompanying factorization equation is selected from the conjunction.

## Where the brief, the DAG or earlier work was wrong

The upstream slicing theorem now returns affineness of each intermediate chart
and a section for each connected-fibre morphism before the factorization equation.
The archived destructuring bound `hfac` to the remaining conjunction, so `hfac i`
failed with “Function expected”. Extracting the typed factorization equation from
that conjunction restores the original mathematical argument without changing any
statement or weakening any hypothesis. A first positional adaptation did not match
the published compile snapshot, which has fewer trailing fields than the current
source. Propositional extraction works for both versions of the same chart theorem.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
