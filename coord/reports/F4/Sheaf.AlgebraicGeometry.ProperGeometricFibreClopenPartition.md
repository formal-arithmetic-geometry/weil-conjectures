## What changed

Implemented the Stein-factorization and étale-splitting construction of
`AlgebraicGeometry.Scheme.Hom.exists_etale_geometricFibre_clopen_partition` with its
signature unchanged. The proof chooses an affine open neighbourhood, applies the existing
affine Stein and finite-residue-field theorems, applies integral-fibre étale splitting,
constructs the map from the total pullback to the intermediate Stein pullback, verifies
its cartesian square, and pulls back the finite clopen partition. Covering, disjointness,
closedness, étaleness, and the marked-point equality are proved in the item module.

The one remaining step is isolated in `GeometricFibreConnectedPreimage`: for a
geometrically connected map, a purely inseparable singleton fibre in an open of its
target has connected nonempty geometric inverse image. This has no proper-family,
étale-neighbourhood, integrality, or finite-partition existence conclusion. It serves
only the final single-piece connectedness step, so this is a genuine decomposition.

## Proved and sorry left

Original holes: 1. Closed in the item:
`AlgebraicGeometry.Scheme.Hom.exists_etale_geometricFibre_clopen_partition`.

Added holes: 1, in the new public theorem
`AlgebraicGeometry.Scheme.Hom.isConnected_geometricFibre_preimage`, node
`lem-weil-pbc-geometric-fibre-connected-preimage`. No holes remain in the item module.
This is a decomposition, with net zero holes closed; imported theorems retain their
existing proof status.

## No longer needed

No existing public import was removed. The original proper-base-change, Stein-factorization,
Stein finite-fibre, and integral étale splitting dependencies are used. The radicial,
purely inseparable extension, algebraic closure, fibre, field extension, geometric
connectedness, and connected-space inputs of the original plan remain necessary in the
single-piece helper; they have been assigned there rather than pruned. No existing module
or declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG marks the radiciality argument elementary, but its Lean implementation needs
compatibility of fibre residue fields, universal injectivity under field extension, and
pullback/open-subscheme identifications. Those are isolated as one single-piece theorem.
The affine and integral assertions from splitting concern the intermediate Stein scheme,
not the total proper family; the proof preserves that distinction.

Edge cases checked: a projective connected family does not require affine total pieces;
the empty marked fibre allows m=0; a nontrivial purely inseparable extension still gives
one geometric point; a separable extension would not satisfy the helper's hypothesis;
nonreduced singleton fibres are permitted. The helper's unique-point assumption excludes
an empty piece. The unit's statement and proof steps are unchanged.

## New nodes

`lem-weil-pbc-geometric-fibre-connected-preimage`, in
`Sheaf.AlgebraicGeometry.GeometricFibreConnectedPreimage`, records the single-piece
radiciality and geometric-connectedness step of Tag 0BUI. Its docstring gives the proof
and the node records the three actual library searches. No existing signature changes.

Change record: `coord/changes/geometric-fibre-connected-preimage.md`.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
