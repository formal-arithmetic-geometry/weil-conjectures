## What changed

Added `ProjGradedModuleChartBasisComparisonFixed`, an intermediate fixed-chart theorem carrying the parent theorem's hypotheses and conclusion for one chart. The parent theorem now introduces the chart and applies this intermediate theorem.

## Proved and sorry left

The parent declaration `AlgebraicGeometry.Proj.gradedModuleChart_basisComparison` is proved by a complete Lean application of the fixed-chart theorem. The intermediate declaration `AlgebraicGeometry.Proj.gradedModuleChart_basisComparison_fixed` remains `sorry` (node `lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed`).

## No longer needed

No imports or planned dependencies were removed.

## Where the brief, the DAG or earlier work was wrong

The parent proof plan requires a substantial fixed-chart construction; this delivery makes that missing step an explicit intermediate node.

## New nodes

`lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed` records the fixed-chart intermediate theorem and its source.

## Second reading by K1

1. Statements and interfaces: compared the delivered parent module byte-for-byte with the repository version; the theorem signature is unchanged. The added fixed-chart theorem is a strict fixed-`f` specialization with the same hypotheses and conclusion, and its node matches the Lean declaration. Verdict: pass.
2. Proof and axioms: compiled both modules with `lcompile.py --all`; the parent proof is a direct application of the fixed-chart theorem. The fixed-chart theorem is the only remaining named `sorry`; no `sorry` occurs in a definition, and no forbidden declarations were added. Verdict: pass, with the fixed-chart node explicitly recorded as split.
3. Existing declarations and novelty: searched the repository for the fixed-chart declaration and related names; no duplicate theorem exists. The parent declaration remains unchanged. Verdict: pass.
4. Pruning and route: the parent now uses the fixed-chart node directly, so its DAG proof dependencies were updated accordingly. The fixed-chart module retains only the imports needed for its statement. No prior imports were removable from the parent beyond the proof-only fixed-chart import. Verdict: pass.
5. DAG and unit agreement: updated the parent node's proof, proof dependencies, and proof origin to record the direct application; the fixed-chart node records its split proof and source. The unit route remains through the parent chart-basis comparison. Verdict: pass.

Changed the parent proof to apply `gradedModuleChart_basisComparison_fixed`, added its proof-only import, added the fixed-chart module and node, and updated the parent node metadata. The fixed-chart construction remains open as the documented split theorem. The change record is `coord/changes/gradedModuleChart_basisComparison.md`.
