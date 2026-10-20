## What changed

Completed the retirement explicitly listed in coord/retire-items.tsv for
Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationGenericComparison.
The duplicate module is withdrawn through deleted.txt. Its existing DAG node
lem-sbc-stalk-normalization-generic-comparison now points to the proved theorem of the same
name in WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationGenericComparison.

The two direct consumers, StalkNormalizationTraitCharts and
StalkNormalizationTraitDivisorCharts under Sheaf.AlgebraicGeometry.Morphisms, now import
the canonical module privately. Each application omits hS and hηU, the only hypotheses
absent from the canonical signature. Their public theorem statements are unchanged.
The three-step comparison argument and the spreading unit route are unchanged.

Change record: coord/changes/G7-stalk-normalization-generic-comparison-retirement.md.

Validation: lcompile.py --all compiled both adapted modules on the project server,
StalkNormalizationTraitCharts in 8.5 seconds and StalkNormalizationTraitDivisorCharts
in 24.2 seconds. The delivery gate requires warning-free compilation, so the chart theorem locally disables
only the unused-variable linter to retain its hS and hηU binders. This matches the existing
scoped linter option on the divisor-chart theorem. Source comparison confirms that the
only consumer changes are the private import, theorem application, and this local linter
option and explanatory comment.
The DAG node differs only in its Lean attachment. No quarantined Lean file imports the
withdrawn module or mentions its theorem.

## Proved and sorry left

The item already had zero textual sorry holes. This is a duplicate-retirement repair,
not a newly closed proof: 0 holes closed, 0 holes added, 0 split off, 0 holes left.
No delivered Lean module contains sorry. The canonical
AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_generic_comparison is proved;
the consumer theorems GaloisCover.stalk_normalization_trait_charts and
GaloisCover.stalk_normalization_trait_divisor_charts retain their complete proofs.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationGenericComparison.
Removed its private proof import from both direct consumers and replaced it with
WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationGenericComparison.
The private duplicate helper normalization_iso_of_iso_over is removed with the module;
the canonical module contains its own proved helper and full comparison proof.

No mathematical node is pruned. In particular,
lem-sbc-stalk-normalization-generic-comparison remains needed by the two chart nodes,
and its three proof dependencies remain needed by the canonical proof:
lem-sbc-stalk-generic-open-pullback, lem-sbc-galois-cover-base-change, and
lem-sbc-normalization-stalk-base-change. Their canonical modules remain imported upstream.
The withdrawal is justified by an actual canonical replacement, not by a count of importers.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a deep outstanding obligation, but the current module
has been fully proved since the earlier S3 delivery. The specific current assignment is
the zero-hole retirement in coord/retire-items.tsv. The bulk retirement kept this module
because its signature differs from its upstream twin: the Sheaf version retains the unused
hS and hηU arguments. Those differences require only the two explicit consumer adaptations.
The DAG Lean attachment was still pointing at the duplicate; it now names the canonical
proved source declaration. The canonical theorem establishes the full conclusion under the hypotheses
of the unchanged node text.

Searches used msearch.py with leanfinder, loogle and grep; direct rg of both source roots
found the canonical theorem and exactly the two direct Sheaf consumers. LeanFinder returned eight Mathlib normalization API results, without the bundled
comparison. The loogle and grep search wrappers returned zero hits; the canonical source text supplies
the exact match. No new statements, nodes, arbitrary chosen data, or axioms are introduced.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
