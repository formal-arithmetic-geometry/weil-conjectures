## What changed

Proved `AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_geometricallyConnected`
in `Sheaf.AlgebraicGeometry.GeometricallyConnectedImageCriterion`, with its signature unchanged.
The proof realizes the existing six-step DAG plan: receive each finite separable extension in
one finite Galois extension, obtain connectedness of the source base change, construct an
invariant clopen separation if the target base change were disconnected, descend it and
contradict connectedness of the original target, then descend connectedness along the
surjective base-change map and apply the finite separable test.

Added proof imports of `Sheaf.AlgebraicGeometry.GaloisConnectedImageInvariantSeparation` and
`Sheaf.AlgebraicGeometry.GaloisInvariantClopenPartitionDescent`. All public imports are
preserved. Updated the item's fifth DAG proof step to identify the projection by
`baseChangeMap` and `isPullback_baseChangeMap`; the dependencies and unit route are unchanged.

Remote single-file compilation passed cleanly in 4.1 seconds. The delivery tool also checks
compilation and declaration axioms. The identity extension is allowed throughout; source
nonemptiness supplies target base-change nonemptiness before the clopen criterion is used.
No finite-type, quasi-compactness, or surjectivity assumption on the original morphism is used.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_geometricallyConnected`
(node `lem-trf-geometrically-connected-image-criterion`).

Item holes remaining: 0. New holes added: 0. Split-off statements: 0.
This is a proof from existing stated dependencies, not a new decomposition.
The imported existing theorems `AlgebraicGeometry.galois_connected_image_invariant_separation`
(node `lem-trf-galois-connected-image-invariant-separation`) and
`AlgebraicGeometry.existsUnique_clopen_partition_of_galois_invariant`
(node `lem-trf-galois-invariant-clopen-partition-descent`) still have their existing holes;
this delivery does not change them or claim to close them.

## No longer needed

Removed direct proof imports
`WeilConjectures.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends` and
`WeilConjectures.AlgebraicGeometry.BaseChangeConventions`.
The first is supplied and used through the partition-descent dependency; the second is
already supplied publicly by the dependencies. Their modules are still transitively needed.
No DAG dependency or module is globally pruned: every declared proof dependency is used,
either by the two substantial stated steps or by the parent assembly.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement defect was found. The original module's imports predated the
DAG split into the two invariant-partition steps; this delivery imports those stated lemmas.
The fifth step's explicit iterated-pullback identification can be implemented directly by
the existing cartesian base-change map, without constructing a separate pullback isomorphism.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
