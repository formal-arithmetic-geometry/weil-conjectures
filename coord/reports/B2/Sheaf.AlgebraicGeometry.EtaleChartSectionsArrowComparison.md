## What changed

Added `EtaleChartSectionsObjectComparison.lean`, splitting the compatible object-isomorphism square into a named intermediate theorem with `sorry`. The target module imports it and proves `nonempty_etaleChartSections_arrowIso` by `Arrow.isoMk`.

## Proved and sorry left

`AlgebraicGeometry.Etale.nonempty_etaleChartSections_arrowIso` is proved. `AlgebraicGeometry.Etale.etaleChartSections_objectComparison` remains `sorry` (node `lem-sbc-etale-chart-sections-object-comparison`).

## No longer needed

No imports or planned dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The planned proof requires a substantial compatibility square not available as a declaration. It was split into the object-isomorphism compatibility theorem; the target proof is complete from that strictly smaller statement.

## New nodes

`lem-sbc-etale-chart-sections-object-comparison` records the intermediate compatible object-isomorphism square.

## Earlier second reading (a previous round; superseded)

The target declaration is unchanged and follows from the intermediate theorem via the standard `Arrow.isoMk` constructor. The intermediate statement is strictly the compatible object-isomorphism square required by the proof plan, and the unit route remains represented.

## Second reading by B2

1. I compared both delivered modules with the repository versions. The target signature is byte-for-byte unchanged; the added module is a new split node and no existing declaration was altered.
2. Both files compile locally with `lcompile.py --all`; the only remaining `sorry` is the named intermediate theorem, and there are no axioms, unsafe declarations, or hollow definitions.
3. The split theorem states the object isomorphisms and their commuting square, which is the strict intermediate data consumed by `Arrow.isoMk`; its source, proof description, and node are recorded in `lem-sbc-etale-chart-sections-object-comparison`.
4. The target proof uses that intermediate data and `Arrow.isoMk`; no shorter existing declaration was found, and the imports remain minimal for the declarations used.
5. The DAG proof and `proof_deps` match the Lean proof, and the degree-zero unit route remains represented. I changed only this report section; no pruning was possible.
