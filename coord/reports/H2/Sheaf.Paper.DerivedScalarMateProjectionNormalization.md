## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.DerivedScalarMate.scalarMate_projection_normalization`
by the geometric adjunction calculation from the DAG's second step. The proof identifies the
B-transpose of beta with lambda followed by extension of the A-counit, applies the published
`proEtaleRingSheafChangeAdjunction`, moves the counit through the normalized tensor
identification by naturality, and cancels the source identification. The resulting transpose
is the defining projection mate. All original signatures, definitions and public imports
are unchanged.

The pullback-only identity from the DAG's first step is stated in the new proof dependency
`Sheaf.Paper.DerivedScalarPullbackTensorNormalization`. It has no direct image, geometric
counit, beta, projection morphism or isomorphism-locus assertion. Thus it is strictly a part
of the argument, rather than a renamed version or repackaged hypothesis of the item.
The item's node now records the actual argument and its dependency on this smaller step.

## Proved and sorry left

One original hole is closed in the item's Lean body:
`AlgebraicGeometry.Scheme.DerivedScalarMate.scalarMate_projection_normalization`
(node `lem-sfb-derived-scalar-projection-normalization`).

One new hole is added:
`AlgebraicGeometry.Scheme.DerivedScalarMate.scalarPullback_tensor_normalization`
(node `lem-sfb-derived-scalar-pullback-tensor-normalization`). Its proof is exactly
`by sorry`, with the source and complete representative/localization argument in its
docstring and node. There are zero holes left in the item module, one in the new module.
This is a decomposition (one hole closed, one added, net zero), not a claim of a
sorry-free transitive proof. The pre-existing `derivedTensorIso_existsUnique` in
`DerivedScalarMateData` is an unchanged dependency, not an added hole.

Both delivered modules compiled without warnings through `lcompile.py --all`: 3.3 s for the
new pullback-only module and 17.1 s for the item, below the 60 s per-file limit.
The new statement preserves arbitrary ring sheaves, arbitrary derived inputs and arbitrary
normalized tensor presentations. Empty schemes and zero ring sheaves are included.
No flatness of B is imposed: only the resolved first factor needs to be K-flat.
The coefficient is in degree zero, so the pure-tensor comparison introduces no sign.

## No longer needed

No original import or node is pruned. The original scalar normalization, tensor-pullback,
and resolving-descent dependencies remain needed by the new pullback-only node.
The existing public import of `DerivedScalarMateData` is retained; the new lemma is a
private proof import of the item. No source-library declaration is removed or modified.

## Where the brief, the DAG or earlier work was wrong

The second proof step's reference to “step 2 with M=RK” meant the first step's
pullback/tensor identity. The updated proof describes this reference explicitly.
The supplied dependencies give the separate scalar, tensor and localization
normalizations, but none states their combined pullback-only equality for arbitrary
ring sheaves. The constant-coefficient `ProEtaleScalarTensorNormalization` has narrower
coefficients and imports a parent of this item, so it cannot be used here without a cycle.
It was quarantined during this session and remains preserved at its current rework path;
this delivery does not withdraw or modify it.
The quoted Stacks tags provide the constructions; the equality between their prescribed
normalizations is the agent-written compatibility calculation already identified in the
original node, and is labeled as such in the new node.

## New nodes

`lem-sfb-derived-scalar-pullback-tensor-normalization` states the first proof step before
taking geometric mates, with the precise coefficient identification needed by targetIso.
It is attached to the single new module above. Its five proof dependencies are the
original first step's declared scalar-adjunction, scalar-normalization, tensor-pullback,
scalar/tensor-identification and resolving-descent nodes. The unit route is unchanged.
No change record is needed: no existing statement, definition or importer interface changes.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
