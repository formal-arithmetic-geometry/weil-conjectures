## What changed

Proved `AlgebraicGeometry.Scheme.affine_direct_image_support_bound` with its original
signature and public imports. Every new helper is private and proved. The proof follows
the assigned compatible-model route: form the affine base-change diagram by pullback in
over categories, prove algebraicity of its residue extensions using the existing
fibre-product residue-field theorem and integral base change, apply the transcendence-degree
tower formula, and use affine support vanishing. The negative complementary bound gives
empty support instead. The fixed-base cohomology cocone transports vanishing to the limit;
the Ext/derived comparison and strict-henselization stalk formula finish the support estimate.
This covers degree zero, degrees above the original bound, and empty schemes.

Added proof-only imports for the existing cohomology cocone, Ext/derived comparison,
residue-field comparison, finite residue transcendence degree, torsion pullback, and
Mathlib's integral-morphism and over-category limit APIs. Updated the existing node's
proof, proof dependencies and proof origin to this implemented argument. The additional
existing tools from the proper-base-change unit are the cohomology cocone, the Ext/derived
comparison, the fibre-product residue-field theorem and the isomorphism case of cohomology
topological invariance; the maintainer records any additional tool-use approvals.

Validation: the entire geometric-stalk argument compiled as proved private helpers before
assembly. The final module is compiled and checked by the required delivery dry run.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.affine_direct_image_support_bound`
(node `lem-kun-affine-direct-image-support-bound`).

Holes closed: 1. Holes added: 0. Actual holes left in the delivered module: 0.
No new module or obligation is split off. The proof uses the declared dependency theorems,
including their existing admitted proofs, as required by stage 3.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.CofilteredEtaleCohomologyContinuity`:
the existing fixed-base cocone theorem supplies exactly the colimit needed, with no separate
construction of a compatible sheaf diagram. Thus node
`lem-weil-pbc-cofiltered-etale-cohomology-continuity` is no longer a direct proof dependency;
its old entry in `tool_uses` is removed. This is a local dependency removal, not a claim that
no other target path needs that node.

Removed `Sheaf.AlgebraicGeometry.TorsionSheafCharacterizations`, the retired compatibility
re-export; the proof directly imports and uses the canonical source module
`WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations`.
Removed the redundant direct import
`Mathlib.RingTheory.AlgebraicIndependent.Transcendental`; its results are publicly supplied
by the retained `Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis`.
All other declared dependencies are used. No unit statement or realized unit step is bypassed.

The previous attempt's unlanded node
`new-kun-affine-direct-image-geometric-stalk-vanishing` is not delivered: its remaining
argument is now fully proved as private helpers. The old drafts are retained in the sandbox
scratchpad; no existing library module or DAG node is deleted.

## Where the brief, the DAG or earlier work was wrong

The previous attempt replaced the support estimate by an admitted geometric-stalk estimate
with the same mathematical content. That is not a strict reduction. This delivery proves
that estimate, including its model construction, residue calculation and continuity step,
and adds no admitted replacement. The previous node also had missing search metadata and
an out-of-date recorded signature; it is unnecessary and is not delivered. The earlier
unscoped `open CategoryTheory.Limits` change is replaced by declaration-scoped openings
on private proof helpers, preserving the original module context.

The mathematical route of the assigned DAG is retained. Its continuity step is implemented
through the already stated fixed-base cocone API, rather than manually supplying all the
data of the general compatible-sheaf continuity theorem. No statement or definition repair,
consumer adaptation, or new node is needed.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
