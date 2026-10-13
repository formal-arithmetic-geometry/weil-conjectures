## What changed

The unchanged target `GaloisCover.regular_divisor_prescribed_punctured_root_chart`
now uses the existing `GaloisCover.regular_divisor_root_splitting`, followed by the
new `root_split_cover_prescribed_cyclic_charts`. The proof constructs the factorization
through D(g), transports the divisor-point condition, composes the pointed etale maps,
pastes pullbacks, and verifies that the final equation is the image of the original f.
Both additional imports are plain proof imports.

## Proved and sorry left

Closed the target hole
`AlgebraicGeometry.Scheme.GaloisCover.regular_divisor_prescribed_punctured_root_chart`.
Added one hole `AlgebraicGeometry.Scheme.root_split_cover_prescribed_cyclic_charts`
(node `lem-sbc-root-split-cover-prescribed-cyclic-charts`). The already existing
`GaloisCover.regular_divisor_root_splitting` remains open in the imported library.
This delivery is a decomposition, not an axiom-free proof or claimed net hole reduction.
The first worker's two proposed holes `GaloisCover.exists_prescribed_punctured_root_chart_core`
and `etale_regular_divisor_base_change` have been removed from the delivery.

## No longer needed

Removed the proposed proof imports and new modules `PrescribedPuncturedRootChartCore`
and `EtaleRegularDivisorBaseChange`, and their proposed nodes
`lem-sbc-prescribed-punctured-root-chart-core` and
`lem-sbc-etale-regular-divisor-base-change`. Neither was in the repository baseline.
The baseline target node had no proof dependencies, so none of its old nodes were pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker's core lemma repeated nearly the entire target, omitting only regularity
properties automatic under etale base change. Its documentation was a description of
an argument rather than a complete proof. Both new node searches and proof texts were
also copied indiscriminately between the two statements. The library already supplies
the substantive ramification-killing stage as `regular_divisor_root_splitting`.
`RootSplitCoverCyclicCharts` supplies classification with an arbitrary final equation,
which cannot prove that the target equation is the prescribed image of f. The new lemma
states only classification for an already root-split cover, without Galois, torsor or
invertible-group-order hypotheses. Its docstring explains the intermediate-root argument
and descent while retaining the equation.

## New nodes

`lem-sbc-root-split-cover-prescribed-cyclic-charts` records the classification step for
a cover already split by a single positive unit root extension. It is a generic
scheme-theoretic descent tool, not the original torsor construction. Its module is
`Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverPrescribedCyclicCharts`. No change
record is needed: no existing signature or definition changed.

## Second reading by G2

1. Compared the target against the repository using diff. Its theorem signature is
byte-for-byte unchanged. No existing definition or other declaration changed. Pass.

2. Read every delivered declaration. The target contains a genuine assembly proof;
the only delivered sorry is the named classification theorem documented and recorded
above. There are no definitions, arbitrary chosen data, axioms, unsafe or external
implementations in the delivery. Compilation and axiom checks are recorded below.

3. Repeated LeanFinder, Loogle and grep searches with cyclic-descent and root-splitting
queries, and read the related library declarations. Reused the existing root-splitting
lemma. The classification statement is strictly a part of the argument: it assumes
an explicit splitting rather than producing one from a Galois ramification bound.
Its proof uses cyclic orbits and intermediate roots in the strict henselization,
then finite-presentation descent. Checked n=1, empty covers d=0, and the divisor point
condition; the latter excludes zero-ring and unit-equation edge cases. Pass.

4. The target proceeds downward by the existing root-splitting declaration and the
prescribed classification step. Plain imports are used for both proof dependencies.
Every new proof import is used, and all public baseline imports provide statement
vocabulary. The unit record sk-prop-input-spreading has empty realized arrays in the
baseline; this delivery does not change them or bypass any recorded unit step. Pass.

5. Checked the target's three proof steps and dependency union against the Lean proof.
The new node includes the matching verbatim signature, source, complete argument,
search records, provenance, chapter, unit, and split status. Pass.

Second reading replaced the near-restatement and redundant base-change split with
existing root splitting and one prescribed-equation classification split, and wrote
the actual pullback assembly and composite-equation calculation.

Verification: both delivered modules compile through lcompile.py. Scratch copies with
`#print axioms` show exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`
for both declarations; the latter is expected from the named open classification and
existing root-splitting theorems. No extra axiom is present.

LeanSearch was also attempted for the classification statement; its service returned
an Internal Server Error, recorded as unavailable without a mathematical verdict.
