## What changed

Proved `AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections_chart_preimage` in
`Sheaf.AlgebraicGeometry.ProjectiveMorphismChartPreimage`, with its signature and public
imports unchanged. The selected integral pair is converted from tensor pullback to usual
pullback by uniqueness of left adjoints, preserving each coordinate section through the
unit comparison. The existing source-library chart recognition, frame and coordinate-ratio
lemmas then prove the integral claims. The projection identity transports both opens and
scalars to projective space over S. Cancellation by the chart frame proves scalar uniqueness.
Two proved private helpers handle equality of appLE maps and the ratio comparison.

The file compiles without warnings through lcompile.py (resumed validation: 34.0 seconds).
After one delivery compile timed out, a full-file diagnostic profile compiled in 10.2
seconds; the same file with the exact delivery axiom probe compiled in 11.9 seconds
and reported SHEAF-PROBED 1 with no forbidden axioms. Profiling options are confined
to scratchpad files and are absent from the delivered module. The two new proof
imports pass import_direction.py. The argument applies to n=0, empty Y, zero coordinate
sections and l=j: no nonemptiness or nonzero-section assumption is added, and free-generator
cancellation remains valid on an empty chart.

Updated the item's DAG proof to this route. Three new DAG records attach already proved
source declarations; no new Lean module, public declaration, definition or axiom was added.
The sk-thm-reduction unit's statement and realized steps are unchanged.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections_chart_preimage`
(node `lem-weil-pbc-projective-morphism-chart-preimage`).

Sorries left in the item: none. Holes added: none. Split-off proof obligations: none.
The three newly recorded dependencies already have complete source-library proofs.

## No longer needed

Removed these proof imports:

- `Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistingSheafCharts`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `Sheaf.Paper.NonvanishingSectionTrivializes`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
- `WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes`
- `WeilConjectures.AlgebraicGeometry.TensorPullback`
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`

The item's proof no longer directly needs nodes
`lem-weil-pbc-projective-space-functor-of-points`,
`lem-weil-pbc-projective-space-twisting-sheaf-charts`,
`lem-weil-pbc-invertible-pullback-tensor`, or
`lem-weil-pbc-nonvanishing-section-trivializes`.
Their corresponding modules are among the removed imports above. The chosen integral pair
is already provided by `integralHomOfGeneratingSections_spec`; the source chart API supplies
frames, generating loci and ratios without a fresh residue-field calculation or the large
integral twisting-sheaf chart package. The normalized tensor-pullback section adjunction
module is unnecessary: compatibility with the chosen adjunction follows directly from
Mathlib's `unit_leftAdjointUniq_hom_app`.

These are removals from this item's proof route; other modules may still need them.
The three original public imports remain necessary for the unchanged signature. Added only
proof imports of `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination` and
`WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus`.

## Where the brief, the DAG or earlier work was wrong

The planned fibrewise argument is valid, but longer than the existing source-library route.
The source already proves the required chart recognition, free frame and ratio identities
for every morphism equipped with a section-preserving usual-pullback isomorphism. Those
three results lacked individual DAG records; this delivery records them without restating
or reproving their Lean declarations. The assigned theorem and all its hypotheses are
unchanged. No definition repair or forced consumer adaptation is needed.

Read Stacks constructions.tex, lemma-converse-construction (01N8), the chart construction
and uniqueness paragraphs, and lemma-projective-space (01NE) with the paragraph after
Definition 01NF. The proof preserves that route through the integral pair and chart frames.
The local-generating/nonvanishing bridge is an already proved tool from another unit;
it is used only to identify the two conventions for the section's locus, and does not
replace a step of the reduction unit.

## New nodes

`lem-weil-pbc-projective-pair-chart-frame` records the existing source declaration
`AlgebraicGeometry.ProjectiveSpace.isFreeGenerator_of_twistRestrict_iso` in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible`. A section-preserving
isomorphism carries the pulled-back coordinate frame to s_i on its chart.

`lem-weil-pbc-projective-pair-chart-relation` records the existing source declaration
`AlgebraicGeometry.ProjectiveSpace.map_eq_coordRatio_smul_of_twistRestrict_iso` in the same
module. It transports the coordinate-ratio equation through a module morphism, using
O-linearity and naturality; an isomorphism is not needed for this equation.

`lem-weil-pbc-projective-pair-generating-locus` records the existing source declaration
`AlgebraicGeometry.ProjectiveSpace.generatingLocus_eq_preimage_standardOpen` in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination`. Its chart frames and
ratio equations characterize the preimage of each standard chart as a generating locus.

All three are strictly general source facts, already proved, with no new Lean statements
or holes. The Mathlib search queries were run with msearch.py (LeanFinder, Loogle, grep,
and LeanSearch); source declarations were found with rg and read in full. The blueprint
search `blueprint_refs.py search projective chart` found no duplicate of these universal-pair
lemmas. No change record is needed because no statement, definition or public import changes.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
