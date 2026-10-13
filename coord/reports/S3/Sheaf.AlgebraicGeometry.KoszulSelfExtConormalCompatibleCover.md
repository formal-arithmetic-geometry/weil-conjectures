## What changed

Replaced the sorry in KoszulSelfExtConormalCompatibleCover by a complete Lean proof.
It chooses regular affine charts from hregular, refines each overlap point by point,
uses nested-chart naturality on the refinement, and applies sheaf separatedness to
prove equality on the full common subopen. The original signature and public imports
are unchanged. Added two proof-only imports and two new statement modules.

KoszulRegularAffineRefinement is proved from Mathlib's distinguished-open and ideal-map
API and the existing isKoszulRegular_of_flat. KoszulSelfExtConormalNestedCharts isolates
the remaining normalized comparison construction and its naturality on inclusions.
All three files compile using lcompile.py. No definitions or existing interfaces changed.

## Proved and sorry left

Closed: AlgebraicGeometry.koszulRegularImmersion_self_ext_conormal_compatible_cover
(new-s3-koszul-conormal-compatible-cover), the only original sorry.

Added and proved: AlgebraicGeometry.koszulRegularImmersion_affine_refinement
(new-s3-koszul-regular-affine-refinement); this adds no hole.

Added and still sorry: AlgebraicGeometry.koszulRegularImmersion_self_ext_conormal_nested_charts
(new-s3-koszul-conormal-nested-charts). Its proof is exactly `:= by sorry`.
There are no other sorries in this delivery. This is a decomposition: one upper hole
closed and one lower hole added, not a claim to have finished the normalized Koszul
comparison theory or removed its transitive sorry dependencies.

The remaining theorem is a chart-level inclusion assertion, with no regularity
assumption on V, no point-indexed cover, and no compatibility of nonnested charts.
The delivered proof supplies the missing common-refinement and separatedness argument;
it does not merely apply a renamed cover theorem.

## No longer needed

No existing imports removed. No globally pruned modules claimed.
The original direct proof dependencies are no longer direct dependencies of the cover
node: new-j3-koszul-projective-resolution (Sheaf.RingTheory.KoszulProjectiveResolution),
lem-sc-affine-quotient-resolution-sheafification
(Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification),
lem-sc-derived-internal-hom-restrict-open (Sheaf.Paper.DerivedInternalHomRestrictOpen),
lem-sc-derived-hom-finite-free-model (Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel),
lem-sc-koszul-conormal-basis (Sheaf.RingTheory.KoszulConormalBasis),
lem-sc-affine-conormal-frame (Sheaf.AlgebraicGeometry.AffineConormalFrame), and
new-q2-koszul-generator-chain-map (Sheaf.RingTheory.KoszulGeneratorChainMap).
They remain planned dependencies of the nested-chart node; they are relocated,
not globally pruned or bypassed. The cover module does not import them directly.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or forced adaptation. Existing local-frame and pointwise-isomorphism
lemmas give no normalization or transition identities, so their existence assertions
alone cannot prove overlap compatibility. Importing the global dual-exterior-conormal
or Yoneda-surjection modules would close an import cycle through this item; neither
is used. The unit realized record contains no assigned statement or step that this
reduction bypasses. The original DAG omitted the explicit regular affine refinement
needed before applying separatedness; it is now a proved node.

The cited Stacks tags were read online (0BQY, 062I, 062H, 01I1, 01HV). LeanFinder,
Loogle and recorded Mathlib grep found useful basic-open and transport tools but no
normalized comparison family. LeanSearch returned Internal Server Error; that is
recorded as unavailability rather than an absence result.

Edge cases: empty V gives an empty chosen cover; empty U uses the empty refinement
cover and separatedness; n=0 and n above local rank are retained in the nested-chart
statement. Refinement preserves the generator length by flat localization, including
the empty sequence, and never assumes intersections of affine opens are affine.

## New nodes

new-s3-koszul-conormal-nested-charts: simultaneous normalized comparisons on regular
affine charts, natural only for inclusions. This isolates the unresolved Koszul
functional-pairing construction and resolution-comparison naturality in
Sheaf.AlgebraicGeometry.KoszulSelfExtConormalNestedCharts.

new-s3-koszul-regular-affine-refinement: a regular affine chart can be refined inside
another affine neighborhood of a point of Z. It is fully proved in
Sheaf.AlgebraicGeometry.KoszulRegularAffineRefinement. No change record is needed.

## Second reading by S3

1. Interface: compared the cover module with the repository using diff. Its entire
existing declaration signature and docstring are byte-for-byte unchanged; only two
plain proof imports and the proof body were added. The other two modules are new.
There is no changed definition, target, or existing public interface and no forced
adaptation. No relevant open change record was found.

2. Proof: compiled all three modules in import order with lcompile.py, without errors
or warnings. A separate scratch module printed axioms for all three declarations.
The refinement theorem uses only propext, Classical.choice and Quot.sound. The cover
and nested-chart theorem additionally use sorryAx, as expected for the reported
nested-chart hole. Inspected the delivered sources: exactly that named theorem has
sorry; there are no definitions or forbidden declarations. In the cover proof, hsmall
uses hx and hy to obtain membership in both affine charts, Q intersects the refinement
with the original common subopen, hc identifies both maps on Q, and the final two
naturality equations and target sheaf separatedness prove equality on U. The choices
are local proof witnesses, never data in a definition.

3. Split statements: read the normalized nested-chart statement and its complete
natural-language proof against Stacks [0BQY](https://stacks.math.columbia.edu/tag/0BQY)
(the zero-differential self-Hom calculation) and
[062I](https://stacks.math.columbia.edu/tag/062I) (the conormal basis).
The argument restricts to regular charts; it needs no regularity outside their inverse
images, no global rank bound, and no affine intersection hypothesis. Localization and
resolution comparison give an intrinsic map on nested charts. This is the unresolved
chart construction and inclusion step, while arbitrary overlap compatibility is
proved in the cover module. It is a decomposition, not a net hole reduction. Empty V,
empty inverse images, the empty sequence, n=0 and degrees above the chart rank cause
no excluded case. The refinement proof uses the actual distinguished-open construction
and [062H](https://stacks.math.columbia.edu/tag/062H) flat preservation; it does not
assume regularity of Uprime. Repeated independent LeanFinder, Loogle and Mathlib grep
searches with Ext/normal-bundle/restriction/localization vocabulary. Local rg also
checked existing self-Ext comparisons, scalar Ext comparisons and the regular dual
Koszul complex: scalar Ext into O_Y is a different coefficient calculation; the
self-Ext local frame lacks transition identities; the global self-Ext comparison
depends transitively on this cover and would be circular. No existing declaration
found closes the nested-chart statement directly.

4. Route and pruning: the cover reduction removes the affine chart construction and
nested transition problem from the top-level proof, but really proves the common
refinement and separatedness argument. Both new imports are proof-only and used.
The original public imports provide its statement's objects and remain unchanged.
Checked the original node's seven proof_deps against No longer needed: all seven are
listed there as relocated, not globally pruned. The unit sk-thm-picard-duality has
realized.statement=[] and realized.steps=[[]]; no assigned unit step is bypassed.

5. Nodes: compared the three Lean signatures with their lean.statement records and
read the proof steps and proof_deps. The cover node cites precisely the nested-chart
family and regular affine refinement; the refinement node cites flat Koszul base
change and records the distinguished-open and ideal-map argument. The remaining
node describes the unresolved construction with its source, dependency plan, search
records, creation and blueprint provenance. Both new nodes have the required fields.
The old cover node changes only the proof-related fields allowed for this delivery.
Verdict: acceptable partial reduction with one original hole closed and one new hole
added; no claim of a completed axiom-free self-Ext comparison.

Changes by the second reader: appended this concrete review and the independent
search/axiom evidence. No repair to the Lean proofs or statements was needed.
