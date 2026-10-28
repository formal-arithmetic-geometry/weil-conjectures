## What changed

Proved `AlgebraicGeometry.Etale.vectorIntegration_baseChange_coordinates` from the
explicit degree-one equation `VectorBundleZeroSection.map_frame_coordinates`.
The item now constructs the pulled-back free-module isomorphism using uniqueness
of left adjoints, proves that its global-section matrices are mutual inverses,
constructs the transpose matrix in GL, lifts the bundle map to the source open,
and uses affine-space extensionality and cancellation of the forward chart.
The original statement, including arbitrary W, is unchanged.

Added `Sheaf.AlgebraicGeometry.VectorBundleMapFrameCoordinates`, with concrete
`pulledFrame` and `framedPullbackMap` constructions and one remaining theorem.
The latter is the generator-equation part of the argument for arbitrary linear
bundle maps of possibly different ranks. Neither construction contains a hole or
chooses arbitrary data from an unproved existence statement.

The item imports the new module privately. All original public imports remain.
The node records the actual construction and its dependency on the generator lemma.

Both files were compiled individually, in dependency order, using lcompile.py.
The item compiled in 16.2 seconds before the final import cleanup. The delivery
preflight supplies the final compile and axiom checks.

## Proved and sorry left

Closed the item's one textual hole in
`AlgebraicGeometry.Etale.vectorIntegration_baseChange_coordinates`
(node `lem-pur-vector-integration-base-change-coordinates`).

Added one hole in
`AlgebraicGeometry.VectorBundleZeroSection.map_frame_coordinates`
(node `lem-pur-vector-bundle-map-frame-coordinates`). This is a decomposition,
not a net reduction in holes: one closed, one added, net zero.
There are zero holes left in the item and exactly one in the new module.

The remaining statement is strictly the individual forward generator equation,
with the module map and its rectangular matrix already specified. It supplies
neither an invertible matrix nor a comparison of inverse scheme charts. The
original theorem's pullback isomorphism, matrix construction, inverse identities,
transpose convention, structural square, lift, extensionality and chart
cancellation are proved in Lean in the item.

Edge cases checked at the statement level: r=0 has no source-coordinate index;
s=0 gives the zero linear map and empty sums; on empty W the same free-module
calculation applies over its zero global ring. No affineness, nontriviality or
Noetherian hypothesis on W was introduced.

## No longer needed

No existing imports, nodes or modules were pruned. The original five stated
proof dependencies remain used. The new module needs only the public import
of VectorTraceGeometry; its redundant AffineLinearTraceAction import was removed.
The open-only overlap-coordinate proof does not supply arbitrary-base-map
naturality and is not imported by this proof.

## Where the brief, the DAG or earlier work was wrong

The planned dependency declarations provide the bundle map's generator equation
and the canonical module pullback comparisons, but none states their combined
coordinate formula in arbitrary pulled-back frames. The remaining new theorem
isolates that precise calculation, rather than another existential GL/inverse-chart
comparison. The matrix in this proof maps source basis sections to target basis
coordinates; its transpose is the required H. This is consistent with taking the
inverse transpose of the opposite frame-transition convention in the old docstring.

## New nodes

`lem-pur-vector-bundle-map-frame-coordinates` states the forward degree-one
coordinate equation for an arbitrary, possibly noninvertible, rectangular module
map, using the actual canonical pullback comparisons. Its source is the original
node's Step 3 and the symmetric-algebra vector-bundle construction in Stacks.
The definitions are explicit compositions of isomorphisms and a module morphism.
LeanSearch, LeanFinder, Loogle and Mathlib grep searches are recorded in searches.jsonl and
in the node. No change to an existing interface outside the item was needed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.VectorBundleMapFrameCoordinates": "5c1a7a74bb124e41c2f45f5e43e1d1fee1d4daeb", "Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeCoordinates": "5ef8eb01b56724cdb37b70e3ee2e3903f9e66594"}, "results": {"Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocalTrace": {"hash": "260a091d3a312e83a5cd87cf32c22e9b85c0d996", "status": "OK"}}, "seconds": 189, "time": "2026-10-28T12:04:43+0800", "transitive": 0, "version": 1}
```

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
