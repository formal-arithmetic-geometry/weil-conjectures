## What changed
Change record: `coord/changes/IsomorphicSingleTensorCounitEquation.md`.

Completed the proof of `AlgebraicGeometry.isomorphic_single_tensor_counit_transport_equation`.
The proof factors the composition-pinned counit on single complexes, applies naturality of the
selected derived adjunction unit, uses the inverse-component equation of the canonical transport,
and cancels the transport inverse/hom pair. The existing transport source module is included in the
sandbox so the dependency chain compiles against the source tree.

## Proved and sorry left

The target declaration is proved with no `sorry` in this item. Its proof uses the existing
(unproved) declaration `exists_isomorphic_single_tensor_counit_transport`; that dependency remains
a separate DAG item. No new holes were introduced.

## No longer needed

None. All imports and dependency nodes used by the proof remain necessary.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt reported a missing `IsomorphicSingleTensorCounitTransport.olean` in the
published build. The source module is present in the repository; placing that source in the
sandbox allows `lcompile.py --all` and `deliver3.py --no-push` to complete. This was a published
artifact issue, not a proof or timeout failure.

## New nodes

None.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader; the proof and dependency source compile in the sandbox.

## Second reading by F2

1. I compared the delivered equation module with the repository version. The public theorem statement is byte-for-byte unchanged; only its proof and proof-only import were added. The transport dependency is identical to the repository source.

2. I checked the module for forbidden constructs and untracked holes. The target theorem has no `sorry`; the only remaining `sorry` is the pre-existing dependency `exists_isomorphic_single_tensor_counit_transport`, which is listed in the report and DAG. No axiom, unsafe, opaque, extern, or implemented_by declaration was added.

3. The proof follows the unchanged target statement and uses the selected composition factorization, single-complex comparison, unit naturality, and the transport inverse-component equation. The intermediate private lemmas are strictly reductions and introduce no public split-off statements or new nodes.

4. Imports are minimal for the proof: the public transport module supplies the target dependencies, while `PinnedPullbackCompositionShifts` is proof-only and is imported privately. The unit route remains the composition comparison followed by transport cancellation; no unit step is bypassed.

5. The DAG node proof and proof_deps match the Lean proof, and the existing unit record is respected. No new node or statement was introduced.

I changed only this report section; no Lean or DAG repair was needed.
