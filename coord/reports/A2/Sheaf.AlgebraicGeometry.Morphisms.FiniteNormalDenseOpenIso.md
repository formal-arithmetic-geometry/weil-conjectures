## What changed

Kept the existing signature and docstring of
`AlgebraicGeometry.Scheme.finite_normal_iso_of_dense_open` unchanged. Replaced the
unreviewed affine/gluing split with a normalization reduction. The new module
`Sheaf.AlgebraicGeometry.Morphisms.NormalizationDenseOpen` states the one remaining
integral-closure obligation. A proved private helper uses Mathlib's canonical
normalization and its universal property to extend a map through a finite
pullback. Applying it to the given isomorphism and its inverse produces two
maps; Mathlib's density/separatedness uniqueness theorem proves they are inverse.
The two added imports in the item are plain proof imports. Its existing public
imports are unchanged. No existing definition or signature changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.finite_normal_iso_of_dense_open`: its proof now has no
local sorry. Added exactly one hole,
`AlgebraicGeometry.Scheme.isIso_fromNormalization_denseOpen`, node
`lem-sbc-normalization-dense-open`, in the new module. The private helper
`AlgebraicGeometry.Scheme.extend_from_normalization` is proved without sorry.
This is a decomposition, not a complete axiom-free proof: one original hole
closed and one smaller hole added, net zero. The target still depends on
`sorryAx` through that explicitly named obligation. Removed the two unlanded
holes `finite_normal_iso_of_dense_open_affine` and
`finite_normal_iso_of_dense_open_glue` from the first worker's proposal.

## No longer needed

No baseline imports or modules were pruned. The original node had no proof_deps.
The unlanded proposal's nodes `lem-sbc-finite-normal-dense-open-affine` and
`lem-sbc-finite-normal-dense-open-glue` are discarded, not counted as pruning of
the library. Neither is needed by the replacement proof.

## Where the brief, the DAG or earlier work was wrong

The first worker's report incorrectly said the target still had a local sorry.
Its affine and gluing statements were preceded by ordinary comments, not
complete theorem docstrings. The gluing statement's hlocal supplies unrelated
local isomorphisms, with no requirement that they extend the given e or agree
on overlaps; its purported gluing proof therefore does not follow from hlocal.
The original global hypotheses make its conclusion true independently, so it
is not a useful strictly smaller gluing obligation. Both new nodes circularly
used the original target as their proof dependency, and the target node had not
been updated. The target's existing 0BQL citation is an analogy rather than an
exact citation: that tag treats connected finite etale covers of a normal
integral base. The replacement reduction uses the relative normalization API
(035I), with normality on the two sources; the new obligation's source and proof
explicitly include disconnected and empty schemes. No target statement changes.

## New nodes

`lem-sbc-normalization-dense-open` states triviality of relative normalization in
a dense open of a normal locally Noetherian scheme. Its complete affine proof
is in its docstring and node: split a Noetherian normal ring into finitely many
normal domains, embed sections of each nonempty dense open in its fraction
field, and use integral closedness. This does not mention a second cover, a
finite morphism to a common base, or an isomorphism to extend. No change record
is needed because no existing signature or definition changes.

## Second reading by A2

1. Compared the delivered item with the repository using diff and checked the
   original declaration signature byte for byte, including visibility. Verdict:
   unchanged; its existing docstring is restored to the target declaration.
   Only its proof, proof imports and a private helper change. No definitions change.
2. Compiled both files through lcompile.py in import order without errors or
   warnings. Checked all delivered Lean source for forbidden constructs and
   holes: exactly the one public named theorem above is sorry. Explicit axiom
   inspection gives only propext, Classical.choice and Quot.sound for the private
   helper; the target and new obligation also have sorryAx, as reported. No data
   is chosen from an arbitrary existence hole: normalization is Mathlib's real
   construction, and the inverse comes from an IsIso proposition, which
   determines it uniquely.
3. The replacement obligation is true and strictly smaller than the original.
   Checked V=top, X empty, V empty (density then forces X empty), finite products
   of normal domains, and opens omitting a closed point: no nonempty hypothesis
   is silently assumed. Density is essential; it ensures every affine component
   meets V. Repeated LeanFinder and Loogle searches using normalization and dense
   open terminology, plus grep of Mathlib, upstream and Sheaf. No exact result;
   the upstream function-field results assume an integral scheme and do not
   directly handle arbitrary dense opens or disconnected sources. LeanSearch
   returned Internal Server Error, recorded as unavailable. The new theorem has
   a full source/proof docstring and matching node.
4. The proof reduces from the target down through Mathlib's normalizationDesc,
   pullback equations and ext_of_isDominant_of_isSeparated. Both proof imports
   are used; the new module imports only the APIs its signature needs. No old
   proof dependency remains unused. Read sk-prop-input-spreading's realized
   record and route: this auxiliary node is below the trait/depth-two model
   comparison, and the unit's statement and steps are untouched.
5. Updated the existing node's proof, proof_deps and proof_origin to the actual
   extension/inverse/uniqueness proof. The only new node matches its exact Lean
   signature, has the required source, complete proof, three search kinds,
   status, creation, blueprint ancestry, chapter and unit. Its proof has no
   circular reference to the target. Verdict: the repaired DAG and Lean agree.

Changed in second reading: removed the defective affine/gluing declarations and
nodes; restored the target's docstring attachment; replaced them by one genuine
normalization obligation and a compiled concrete reduction; corrected the
report's hole accounting and the target DAG record.
