## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.ModuleCechComparisonIsoAffine` by
an unchanged-signature proof using the concrete alpha/beta comparison equation.
The proof chooses an injective resolution, registers enough injectives and the
additivity instance, obtains isomorphisms on homology for alpha and beta, and
cancels the resolution identification followed by alpha using
`CategoryTheory.isIso_comp_right_iff`.

Added `Sheaf.AlgebraicGeometry.ModuleCechBetaAffineQuasiIso`, containing the
strictly intermediate affine-acyclicity assertion for beta. Unlike the item,
it has no cover hypothesis, no proposed comparison map, no canonical-comparison
hypothesis and no module-derived-cohomology target. It concerns the explicit
augmentation into the total complex for any prescribed injective resolution.
Updated the item's DAG proof and dependencies to match this reduction.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.Modules.moduleCechComparison_isIso_of_affine`
(node `lem-sc-cech-comparison-map-iso-affine`). Its entire combination proof
compiles and contains no sorry.

Added one named public theorem hole:
`AlgebraicGeometry.Scheme.Modules.moduleCechBeta_quasiIso_of_affine`
(node `lem-sc-module-cech-beta-affine-quasi-iso`). Its whole proof is `by sorry`,
with the source and complete column-acyclicity proof in the docstring and node.

This is a decomposition: one hole closed and one hole added, net zero holes.
It is not a claim that affine Cech comparison is now independent of sorry.
The existing `moduleCechAlpha_isIso` is still used from its original module;
this delivery changes none of that module's holes.

## No longer needed

Removed the proof import `Sheaf.Paper.CechComparisonMapNaturality` and its node
`lem-sc-cech-comparison-map-naturality`: existence, resolution independence and
coefficient naturality are unnecessary for proving invertibility of a map already
supplied with its canonical-comparison equation. The needed alpha isomorphism
is separately available as `moduleCechAlpha_isIso` in the statement import.

Removed `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray` and its node
`lem-pc-cech-computes` from this item's proof imports/dependencies. Its unspecified
linear equivalence to abelian-sheaf cohomology is not needed by the alpha/beta
argument. This is local pruning of these proof edges, not a claim that no other
target uses these modules. The unit's prescribed spectral-sequence/affine-vanishing
argument remains the proof of the new beta statement; no unit statement or
realized proof step was removed. Both original public statement imports remain.

## Where the brief, the DAG or earlier work was wrong

The original one-step DAG proof assumes that
`nonempty_cechComplex_linearEquiv_H` identifies the particular canonical map.
Its actual Lean statement only supplies a nonempty linear equivalence to
`Scheme.Modules.H`, whereas this item targets `RingedSpace.moduleCohomology`.
The upstream Affine module's implementation notes expressly acknowledge that the
edge map is not identified. Thus that direct application does not establish this
item. The existing node's lead_note already anticipated this gap.

Mathlib semantic and source searches found no ready-to-use beta augmentation
quasi-isomorphism. LeanSearch returned an internal server error, recorded in
searches.jsonl; LeanFinder, Loogle and grep were run successfully. The source
pages https://stacks.math.columbia.edu/tag/01EQ,
https://stacks.math.columbia.edu/tag/01ET and
https://stacks.math.columbia.edu/tag/01XD were read directly.

The new beta statement was checked against the empty index family (both complexes
zero), an affine single open not covering X (affine sections still compute the
restricted resolution), the zero module, arbitrary injective resolutions, and
infinite cover-index sets (products are exact in module categories). None needs a
cover hypothesis. No statement, definition or target signature was changed.

## New nodes

`lem-sc-module-cech-beta-affine-quasi-iso` states the exact beta-augmentation
acyclicity portion of the canonical affine comparison argument. Its three proof
steps are intersection-section exactness, exact products of the augmented columns,
and the bounded first-quadrant total cone argument. It inherits the item's chapter
and unit and cites existing restriction, affine-vanishing and spectral-sequence
nodes. It is stated alone in its new module. No change records are needed.

## Second reading by K2

1. Compared the complete existing module with the repository version using diff.
   The sole existing declaration's signature is byte-for-byte unchanged; there
   are no changed definitions, added hypotheses, weakened conclusions or change
   records. Restored its original docstring to avoid an unnecessary API text change.
   The only public imports are the original statement imports. Verdict: pass.
2. Compiled both delivery modules locally in import order with lcompile.py.
   The item's proof contains no sorry. The new beta theorem is the only delivered
   sorry, exactly a named public theorem with a full docstring argument and node.
   Neither file contains forbidden declarations or hollow definitions. Scratch
   #print axioms checks show only propext, Classical.choice, Quot.sound and sorryAx;
   sorryAx is expected from the new beta theorem and the open comparison inputs.
   Choosing injectiveResolution uses the existing resolution construction; no new
   data definition chooses an arbitrary witness from a holed existence theorem.
   Verdict: pass as a decomposition, not a sorry-free target proof.
3. Read moduleCechBeta and its components, the restricted-resolution theorem and
   affine-open vanishing. Checked empty indices (empty products are zero modules),
   one affine open without a cover (restriction sections resolve F), zero F,
   repeated indices, arbitrary resolutions and infinite indices (coordinatewise
   products of surjections remain surjective with choice). Beta's statement needs
   no cover, canonical-map predicate or derived-cohomology target, and is strictly
   the affine-acyclicity part of the comparison argument. The target additionally
   uses cover-dependent alpha invertibility and categorical cancellation.
   Independently searched with LeanFinder for exact columns implying exact total,
   Loogle for HomologicalComplex₂.total, launcher grep for acyclic totals and
   quasi-isomorphisms of totals, and rg through Sheaf and WeilConjectures for
   augmentations and column acyclicity. No exact existing beta result was found;
   FirstQuadrantRowCollapse and CartanEilenbergAcyclicAbutment do not directly
   identify this concrete augmentation. Read Stacks 01EQ, 01ET and 01XD directly.
   Verdict: pass; the remaining theorem requires a substantial formalization,
   rather than a short application closing it in a few minutes.
4. Read the original proof dependencies and their Lean declarations. The upstream
   Leray result gives an unspecified equivalence to F.H, not invertibility of the
   prescribed c; comparison naturality is unused by this combination proof.
   Both old dependencies are listed above as no longer needed. Imports of the
   beta module retain the prescribed inputs for its open proof. The unit record
   sk-thm-picard-duality.json has no realized statement or step assigned to these
   pruned nodes; its statement and residue/adjunction route are unchanged. The
   new beta proof retains affine vanishing and the double-complex spectral route.
   Verdict: pass; no shorter direct comparison proof was found.
5. Compared the delivered nodes with the Lean declarations and the old node.
   The existing node changes only proof, proof_deps and proof_origin; the new
   node has its exact Lean signature, chapter/unit, sources, creation metadata,
   blueprint ancestry and searches. Its proof dependencies match the restricted
   resolution, affine vanishing, comparison construction and spectral theorem.
   Verdict: pass after clarifying the orientation in the final spectral step.

Second-reading changes: restored the existing declaration docstring; clarified
in the new beta docstring and DAG proof that the shifted augmented bicomplex is
transposed, with the standard total sign isomorphism, before applying the first
spectral sequence whose inner cohomology direction must be resolution degree.
No Lean proof or signature was changed. One hole closed and one hole added remain
exactly as listed in Proved and sorry left (net zero, decomposition).
