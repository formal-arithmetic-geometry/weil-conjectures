## What changed

The unchanged target theorem `exists_etale_complex_first_page_and_abutment` is
proved by assembling functorial abutment presentations, the existing termwise
first-page continuity theorem, and final reindexing. Added the new module
`Sheaf.AlgebraicGeometry.EtaleComplexAbutmentPresentations` for the presentation
interface and a completely proved reindexing helper. Updated the parent DAG
proof and the two new nodes to reflect this route.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.exists_etale_complex_first_page_and_abutment`.
Also proved `AlgebraicGeometry.Etale.reindex_first_page_comparison` directly
from Mathlib's colimit API, with no new proof obligation.

One new hole remains:
`AlgebraicGeometry.Etale.exists_etale_complex_abutment_presentations`
(node `lem-weil-pbc-etale-complex-abutment-presentations`).
This is a decomposition into the construction without geometric continuity
and the existing continuity theorem, not a complete axiom-free proof of
hypercohomology continuity. No sorry remains in the item's module.

## No longer needed

Removed direct proof imports of:
- `Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes`
- `Sheaf.CategoryTheory.ExistsDirectedReindexing`
- `Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial`
- `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`
- `Sheaf.CategoryTheory.HypercohomologyFirstPage`
- `Sheaf.CategoryTheory.KInjectiveBridge`

These are replaced by the continuity and abutment interfaces. Their mathematics
remains needed below those interfaces, so none is claimed as globally pruned.
The reindexing helper no longer depends on `thm-sp-spectral-object-yields`;
its proof uses only Mathlib's final-colimit comparison and colimit universal
properties. No module is claimed to leave the targets' import closure.

The old parent proof dependencies no longer used directly are
`def-sp-kinjective-bridge`, `def-sp-spectral-sequence`,
`def-weil-pbc-etale-cohomology`,
`lem-weil-pbc-etale-cohomology-limit-of-schemes`,
`lem-weil-pbc-filtered-category-directed-cofinal`,
`lem-weil-pbc-hypercohomology-e1-pullback-functorial`, `thm-sp-if-e1`, and
`thm-sp-spectral-object-yields`. These are replaced at the parent level by the
three interface dependencies; their mathematics remains below those interfaces.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox left final reindexing as a second sorry even though
Mathlib's final-colimit API closes it directly. Its report incorrectly said
no direct imports were removed, and it omitted the updated parent DAG node.
Both discrepancies are repaired. The earlier second-reading section describes
a superseded version and has been removed for the independent reader.

Edge cases: finality supplies all colimit comparisons without any nonemptiness
assumption on the reindexing lemma. Negative resolution degrees are handled by
the existing continuity interface. The presentation theorem explicitly covers
p<a: the abutment vanishes and both filtration bounds occur at index zero.
No statement or existing signature is changed; no forced adaptations occur.

## New nodes

`lem-weil-pbc-etale-complex-first-page-reindexing` records the proved transport
of any first-page comparison through a final functor. Its conclusion concerns
only the colimit comparison and contains no geometric or abutment construction.

`lem-weil-pbc-etale-complex-abutment-presentations` records the remaining
functorial spectral and filtration construction without the geometric limit,
quasi-compactness, affine-transition hypotheses, or first-page comparison
isomorphism. Its docstring gives the construction, uniform stabilization,
filtration bounds, quotient kernels, and naturality proof. It is strictly the
construction part of the original argument. No change record is needed.

## Second reading by U2

1. Compared the delivered target module with the repository version. Existing declaration
   signatures are unchanged; the target proof only changes imports and proof terms, and
   the added presentation module and nodes are explicitly listed in the report.
2. Compiled both delivered modules with `lcompile.py`; the target has no remaining
   `sorry`, while the presentation interface contains only the named split-off theorem.
   No forbidden declarations or hollow definitions were introduced. The reindexing
   helper is proved by final-colimit API and uses no extra assumptions. Scratch
   `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`
   for this helper; the presentation theorem and target additionally use
   `sorryAx`, as expected from the recorded remaining construction hole.
3. Checked the split-off presentation statement against its docstring and DAG node. It
   is the construction-only interface needed by the target, with the continuity and
   geometric hypotheses retained in the target theorem; it is strictly smaller than
   the target and has a source and proof plan. The reindexing statement is independent
   and exactly expresses final transport of the first-page comparison.
4. Checked pruning: obsolete direct proof imports were removed and recorded above;
   the continuity and presentation interfaces are the imports actually used. The
   realized unit route remains represented by the parent node and its two proof
   dependencies.
5. Checked DAG/Lean agreement for the parent and both new nodes, including proof
   dependencies, proof origins, module/declaration records, and the unchanged target
   signature. No statement or definition change or forced adaptation occurred.

Corrected the presentation node’s first proof step: it incorrectly mentioned
performing continuity inside a theorem that has no continuity hypotheses. The
step now describes only final reindexing and preservation of the lower bound.
No Lean proof repair was needed. Recorded every old parent proof dependency
removed by the reduction. Repeated semantic search for bounded hypercohomology
convergence and read the existing first-page and pullback interfaces; none
already states the complete presentation interface. Checked the cited
[Stacks construction](https://stacks.math.columbia.edu/tag/015J),
[functoriality](https://stacks.math.columbia.edu/tag/015K), and
[continuity argument](https://stacks.math.columbia.edu/tag/0EZM) online, since
the source text is absent from this machine.
