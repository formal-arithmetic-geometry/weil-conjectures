## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.affineRealizationRawComparison_natural`
without changing its statement. The remaining argument is separated into two
independent squares. `affineRealizationRawEvaluation_pullback` is the raw-to-Ext
square, specified by the structural section formula for its coefficient map.
`affineRealizationComparison_pullback` is the ordinary square for an arbitrary
Ext class, with no raw Hom data. Its proof plan constructs compactness and
absolute separatedness of the fibre products, applies the existing normalized
comparison square to the canonical families, and identifies its ordinary map
with `affineRealizationRestriction`. The main Lean proof obtains the coefficient
map and ordinary square, maps the raw-evaluation equality through the target
comparison by congrArg, and composes those two equations by transitivity.
The existing bundled naturality proof stays unchanged.

The remaining raw-to-Ext presentation compatibility is stated in the new module
`Sheaf.AlgebraicGeometry.AffineRawEvaluationPullback`. It has no ordinary module
cohomology, normalized comparison family, affineness, quasi-compactness or
separatedness in its statement. It is the presentation-and-coefficient part of
the original plan; the item combines it with the independent normalized
comparison square. All added imports in the item are private proof imports.
Existing definitions, signatures and public imports are unchanged.

## Proved and sorry left

Closed the textual hole in
`AlgebraicGeometry.Scheme.Modules.affineRealizationRawComparison_natural`
(node `lem-weil-pbc-affine-cohomology-raw-restriction`) by reduction to the stated
normalized comparison square and the strictly smaller raw-to-Ext square below.
The existing
`AlgebraicGeometry.Scheme.Modules.affineRealizationRawCoherentEquiv_natural`
continues to follow from the unbundled theorem.

Added two named public holes:
`AlgebraicGeometry.Scheme.Modules.affineRealizationRawEvaluation_pullback`
(node `lem-weil-pbc-affine-raw-evaluation-pullback`), and
`AlgebraicGeometry.Scheme.Modules.affineRealizationComparison_pullback`
(node `lem-weil-pbc-affine-comparison-pullback`). Each has its source and complete
argument in its declaration docstring and node. There are zero holes left in
the item and two in the new modules. One hole is closed and two are added:
this is a decomposition, not a net proof gain. Imported obligations are unchanged.

## No longer needed

No existing node or module is pruned. The private import of
`Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization` moves from the item to
the proof dependencies of the new raw-to-Ext lemma; its naturality statement
remains needed there. The original coherent restriction and fixed cohomology
presentation dependencies likewise remain needed below the new node. The second intermediate statement uses the normalized comparison pullback
square and its data.
No source-library declaration or unit realization is removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan combines independent normalization squares in one prose step.
The fixed Ext-to-derived presentation proves additivity and bijectivity, but
has no pullback compatibility theorem. The source modules
`SheafHRightDerivedPullback` and `AbelianDerivedGlobalExtPullback` assert existence
of comparison families; they do not identify them with the fixed
`sheafHDerivedEquiv` used by the actual raw evaluation. Their existential
witnesses cannot simply replace that map. The new lemma isolates the raw-to-Ext
square, including the sectionwise coefficient identification, while the second isolates its canonical ordinary-cohomology specialization.
An attempted proof of the latter constructed compactness, separatedness, the
coefficient map and comparison square; its conversion of the actual canonical
comparisons to the normalized families repeatedly exceeded Lean's conversion
budget. That unfinished glue is left as the second named obligation; its full
mathematical proof is supplied, and the item combines the two independent
squares by an actual congrArg/trans proof.

Edge cases were checked against the defining constructions. The induced chart
map is etale for arbitrary etale charts. Tensor pullbacks of quasi-coherent
modules exist without compactness assumptions. Empty charts and zero modules
give zero groups; degree zero uses the same adjunction-unit section formula.
No nonemptiness, properness or flatness of f is introduced. No definition,
existing statement, public import, source-library file, target signature, or unit
route changes. Kernel-checking experiments on a more expanded derived square
were discarded; no experimental definition change remains in the packet, and
no resource limit is raised.

## New nodes

`lem-weil-pbc-affine-raw-evaluation-pullback` is the raw-to-Ext structural chart
square before the normalized ordinary-cohomology comparison. Its source is the
presentation-and-coefficient part of the parent plan, expanded using Stacks
Tags 01FT (`section-cohomology-sheaves`), 03FD
(`lemma-cohomology-modules-abelian-agree`), 03DR
(`section-quasi-coherent-sheaves`, `equation-quasi-coherent-presheaf`), and 03Q8
(`lemma-higher-direct-images`). These give the presentations and section maps;
the docstring supplies the fixed-map compatibility argument as an agent
expansion. The proved generic `derivedSectionPullback_single_unit` supplies the
unit normalization. Searches using LeanSearch, LeanFinder, Loogle, Mathlib and
local library grep, and the current blueprint found no exact fixed-map square.
No change record is required: existing definitions and statements are unchanged.


`lem-weil-pbc-affine-comparison-pullback` is the ordinary-cohomology half. It
specializes the existing arbitrary-normalized-family square to the canonical
families selected by `AffineCohomologyComparisonData`, with its actual tensor
composition map. It has no raw Hom class or raw evaluation and is strictly a
part of the original statement. Its proof is the explicit canonical specialization
of `qcoherentNormalizedComparison_pullback_square`, with the compactness and
separatedness argument and map identification in its docstring. No new data is
selected from this theorem in a definition: its existential witness is eliminated
only in the proof of the item.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
