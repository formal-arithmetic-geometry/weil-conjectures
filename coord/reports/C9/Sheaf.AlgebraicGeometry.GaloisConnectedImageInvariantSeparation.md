## What changed

Filled the proof of
`AlgebraicGeometry.galois_connected_image_invariant_separation` in
`Sheaf.AlgebraicGeometry.GaloisConnectedImageInvariantSeparation`.

The proof follows all five steps of
`lem-trf-galois-connected-image-invariant-separation`. Spectrum functoriality and
`baseChangeMap_comp` give the opposite composition law and explicit inverse scheme maps.
The two projections, using `baseChange_morphism_projections`, prove equivariance of the
base-changed morphism and hence invariance of its range. Mathlib's
`isConnected_range` and `IsPreconnected.subset_isClopen` choose the part containing that
range. The finite intersection of its translates is clopen by
`isClopen_iInter_of_finite`; its nonemptiness follows from the range, and its complement
contains the other nonempty part. Finally, `Set.image_iInter` and surjectivity of right
multiplication reindex the intersection, and the homeomorphism preserves complements.

All constructions and intermediate proofs are local to the theorem. Its signature,
docstring, public imports, and the DAG route are unchanged. No other module is changed.

Validation: the item compiles through `lcompile.py` in 8.4 seconds, with no warnings.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.galois_connected_image_invariant_separation`
(node `lem-trf-galois-connected-image-invariant-separation`).

Holes closed: 1. Holes added: 0. Holes remaining in the item: 0. Split-off statements: 0.

## No longer needed

None. No imports, modules, or DAG dependencies are pruned. The existing dependencies
supply scheme continuity, connectedness, spectrum functoriality, pullbacks and their
projections, and finiteness of the automorphism group (`AlgEquiv.fintype`).
No additional imports or nodes are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The inverse-image connectedness argument in
step 1 is implemented in its equivalent connected-range form using Mathlib's clopen
containment lemma. The proof uses the finite-dimensionality hypothesis for finiteness
of the automorphism group and makes no additional assumptions on either scheme.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
