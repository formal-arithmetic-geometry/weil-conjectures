## What changed

Replaced the hole in
`AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_local_normal_form`
by a complete combination of two separate geometric steps:

- `projective_bundle_fiber_degree` classifies a line on a residue-field fibre,
  including uniqueness, without extending it to any neighbourhood.
- `projective_bundle_fiber_iso_spread` spreads an isomorphism of two invertible
  modules from one fibre. It has no tautological quotient or integer degree.

Both are new modules with one named theorem each. Their source references and
complete proofs in words are in their docstrings and DAG nodes. The main proof
also proves that integer powers are invertible, constructs the comparison from
restriction to the top open back to the original module using tensor-pullback
identity/composition, and proves the field clause: a neighbourhood of the unique
base point is the top open, and fibre uniqueness compares any two global degrees.
Existing public imports and every existing declaration signature are unchanged.
Only the two new modules are added as private proof imports of the item.

This is a decomposition of the original four-step argument, not a claim that
its remaining geometric steps have been proved. In particular, the new spreading
statement is an independent assertion about any two lines, rather than the local
normal-form statement with its hypotheses repackaged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_local_normal_form`
(node `lem-sfb-projective-bundle-local-normal-form`) by a complete Lean proof from
the two new statements. Its module has zero remaining holes. Both private helpers,
`invertible_integerLinePower` and `nonempty_iso_of_top_restriction`, are proved.

Added two holes, each the entire proof of a public theorem in its own module:

- `AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_fiber_degree`
  (`lem-sfb-projective-bundle-fiber-degree`).
- `AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_fiber_iso_spread`
  (`lem-sfb-projective-bundle-fiber-iso-spread`).

Accounting: one original hole closed, two lower holes added; this is a
decomposition, with net minus one hole, not an unconditional proof of either
geometric step. No definition contains a hole and no axiom is introduced.

## No longer needed

No existing import was removed: the three original public imports are needed by
the unchanged signature, and both new proof imports are used.

The node `lem-sfb-locally-constant-line-twist-identities` and module
`Sheaf.AlgebraicGeometry.LocallyConstantLineTwistIdentities` are not needed by this
argument. It uses constant integer powers only; their pullback/tensor/dual
comparison belongs to the fibre calculation and does not require the identities
for gluing over locally constant degree strata. This removes that planned
dependency from this route, without claiming it is unused elsewhere in the library.

The other former dependencies remain needed by the two geometric steps, whose
node records retain them. In particular, affine-chart triviality, projective-line
classification, quotient geometry, module gluing and tensor pullback serve the
fibre calculation. Properness, polynomial flatness, twist cohomology, fibre-section
lifting, Noetherian approximation, limit fibre products and invertible-module
descent serve spreading. None of those modules is claimed pruned. Spreading also
records the existing residue-field limit and finite-presentation isomorphism
descent lemmas used to descend the given fibre isomorphism at a finite stage.
No source-library declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original statement and its rank bound are preserved. No mathematical error
was found. Existing dependencies do not themselves state either the
higher-dimensional field chart calculation or its neighbourhood-spreading
consequence: the projective-line classification is only dimension one, and
fibre-section lifting requires properness, flatness and first-cohomology
vanishing to be supplied. These are the two substantial parts left explicit.

The arbitrary-base spreading proof needs to descend the fibre isomorphism as
well as the two lines. Its new node explicitly cites residue-field limits and
finite-presentation isomorphism descent for this step. Merely descending the
lines does not by itself provide that isomorphism at a finite stage.

Edge cases checked mathematically: an empty base has no points to test;
residue-field fibres have positive projective dimension because r >= 2; field
bases have exactly one point; negative powers use the actual dual, and nilpotents
do not invalidate the local-ring unit argument. Neither split assumes a reduced,
connected, quasi-compact or Noetherian original base.

## New nodes

`lem-sfb-projective-bundle-fiber-degree`, in
`Sheaf.AlgebraicGeometry.ProjectiveBundleFiberDegree`, isolates the original
steps 1-2 on one fibre. Its proof is the chart/cocycle calculation of Stacks
Tag 0BXJ, with quotient geometry transporting the normalized line and negative
powers. It makes no assertion about extension over the base.

`lem-sfb-projective-bundle-fiber-iso-spread`, in
`Sheaf.AlgebraicGeometry.ProjectiveBundleFiberIsoSpread`, isolates the original
steps 3-4 for M dual tensor N. Its proof uses Stacks Tag 07VK to lift a generator,
proper closed-image shrinking, and Tag 0B8W with finite-presentation isomorphism
descent for arbitrary rings. It neither chooses nor classifies a degree.

Searches used LeanSearch, LeanFinder, Loogle and repository/Mathlib/DAG/blueprint
searches. No matching theorem was found; existing partial results were read.
The original node now records the actual combination of these two steps.
There is no interface change to an existing module and no change record is needed.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
