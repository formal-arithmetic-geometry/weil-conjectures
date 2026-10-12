## What changed

Added an explicit-data linearity intermediate theorem and reduced
`moduleCohomologyFMap_basic_linearity` to it using the canonical data chosen by
`moduleCohomologyFMap`.

## Proved and sorry left

Proved `moduleCohomologyFMap_basic_linearity`.
The intermediate theorem `moduleCohomologyFMapData_map_linear` remains `sorry`;
its proof is the direct module-linearity argument on global-sections complexes,
homology, and resolution comparisons described in its docstring.

## No longer needed

None beyond the imports used by the reduction.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled the full linearity argument into the target. The
explicit map is the natural strictly smaller intermediate statement needed to
make the target proof compile.

## New nodes

`lem-weil-pbc-module-cohomology-fmap-data-linearity`.

## Earlier second reading (a previous round; superseded)

Pending independent second reading.

## Second reading by J1

1. **Statements unchanged.** Compared `BasicPropertiesLinearity.lean` with the repository version. The target declaration signature is byte-for-byte unchanged; only its proof and a proof-only import changed. The added theorem has the explicit `ModuleCohomologyFMapData` parameter and is strictly more specialized than the target.
2. **Proof and axioms.** Compiled both sandbox modules with `lcompile.py --all`; compilation succeeds. The target proof unfolds `moduleCohomologyFMap` through its canonical `Classical.choice` and applies the explicit-data theorem, with no new axioms or unsafe constructs. The explicit-data theorem remains the sole named `sorry`, with a source-based docstring and matching DAG node.
3. **New statement.** Checked the added theorem against the explicit-data construction: its conclusion is exactly module linearity for the map `D.map p`, with no weakened hypotheses or altered definitions. No duplicate Mathlib or upstream declaration was found in the recorded searches.
4. **Pruning and imports.** The new proof uses `ModuleCohomologyFMapData_nonempty` and `moduleCohomologyFMapData_map_linear`; the plain proof-only import is therefore required. No prior proof dependency is unused, and no unit-level route is bypassed: this is the explicit-data reduction of the linearity step.
5. **DAG consistency.** The target node records the explicit-data theorem as its only proof dependency and its reduction proof origin. The new node records the exact theorem declaration, source, proof plan, and split status.

Changed only the target proof, added the proof-only import, and recorded this second reading; no statements or definitions were changed.
