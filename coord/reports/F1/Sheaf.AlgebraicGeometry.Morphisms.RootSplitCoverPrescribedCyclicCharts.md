## What changed

Proved `AlgebraicGeometry.Scheme.root_split_cover_prescribed_cyclic_charts`
from the existing `root_split_cover_cyclic_chart_model` and
`etale_regular_divisor_base_change`. Added their modules as proof-only imports.
`Spec.preimage_map` identifies the prescribed equation with the ring-map image.
The existing signature and all public imports are unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.root_split_cover_prescribed_cyclic_charts`
(node `lem-sbc-root-split-cover-prescribed-cyclic-charts`).
No holes are added, and no sorry remains in the delivered module.
The proof still depends on the existing open theorem
`AlgebraicGeometry.Scheme.root_split_cover_cyclic_chart_model`
(node `lem-sbc-root-split-cover-cyclic-chart-model`), so this is not a
sorry-free proof of the entire import closure. The existing regular-divisor
base-change theorem is already proved.

## No longer needed

The second reader removed both proposed new modules and nodes before delivery:
`RootSplitCoverPrescribedChartDescent`
(`lem-sbc-root-split-cover-prescribed-chart-descent`) and
`EtalePreservesRegularDivisor` (`lem-sbc-etale-preserves-regular-divisor`).
They duplicated existing library interfaces. These were sandbox additions,
not modules pruned from the library. No original import was removed and
no original proof dependency was dropped (the original proof_deps was empty).

## Where the brief, the DAG or earlier work was wrong

The first worker missed two existing results. The cyclic chart *model*, unlike
the arbitrary-equation wrapper, already retains the equation phi(g), and
requires no divisor-point hypothesis. The regular-divisor base-change theorem
already supplies all three regularity conclusions. The proposed decomposition
would have added two unnecessary holes. The repaired proof adds none.
The original DAG plan had no declared proof dependencies; its new route now
records the existing model and base-change nodes.

## Second reading by F1

1. Compared the delivered module against the repository: the existing theorem
signature is byte for byte unchanged, and no definition or public import changes.
No other existing module is delivered; no change record is required. Pass.
2. Compiled locally through lcompile.py and checked the delivery axiom probe.
Only the allowed axioms and inherited sorryAx are permitted; the delivered
module contains no sorry, hollow definition or prohibited declaration. Pass.
3. Read both proposed split-off statements and their nodes. Library search with
root-split/model and regular-divisor/base-change terminology found duplicates.
Removed both new declarations, modules and nodes and used the existing results.
No new statement remains. The existing model handles d=0 and n=1 and is stronger
in allowing points outside the divisor; hy need not be used. Pass after repair.
4. Took the shorter route through the existing chart model and regular-divisor
base-change theorem. Both new imports are proof-only and used. The original
proof_deps was empty. Inspected dag/units/sk-prop-input-spreading.json: its
realized statement and step lists are empty. The root-chart route is retained,
and no realized unit step is bypassed. Pass.
5. Updated proof, proof_deps and proof_origin of the existing node to the two
actual theorem applications and Spec.preimage_map. No statement or Lean
signature in its node changed. No new nodes remain. Pass.

Second-reading changes: removed both duplicate split-off modules/nodes, replaced
the proof by existing library applications, corrected the report and DAG route.
