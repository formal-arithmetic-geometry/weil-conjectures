## What changed

Proved `WeilConjectures.FiniteFieldDatum.frobenius_open_square` in
`Sheaf.AlgebraicGeometry.FrobeniusOpenSquare`, with its signature unchanged.
The scheme square is proved directly after base change: the base-changed open
immersion has image equal to the inverse image of the model open, and the
Frobenius preserves this image because its first projection is model Frobenius,
which is identity on points. Naturality is proved from `map_pow` on sections.
Mathlib's open-immersion pullback criterion then applies.

The Galois square uses the existing `galoisMap_inverse` and
`galoisMap_projections` declarations. Projection comparisons prove naturality,
and the horizontal arrows are isomorphisms. Pullback pasting proves every
iterate of both squares. A separate proved induction propagates semilinearity.
All six local helper theorems are private and proved. No definitions, public
signatures, public imports or consumers were changed. The node proof and its
proof dependencies now describe this route. No change record is needed.

The final module compiled cleanly through `lcompile.py` in 4.3 seconds after
removing the unused import. Its generic inductions explicitly include the
zeroth iterate, and the image argument includes the empty open and arbitrary
schemes; no finite-type assumptions were introduced.

## Proved and sorry left

Closed 1 of 1 holes: `WeilConjectures.FiniteFieldDatum.frobenius_open_square`
(node `lem-trf-frobenius-open-square`). No sorry remains in the item module.
Added 0 holes; split off 0 statements. The proof uses the previously stated
`galoisMap_inverse` and `galoisMap_projections`, and the existing
`model_characteristic` and `model_frobenius_over` interfaces. Their independent
proof obligations remain in their existing modules; none is copied or added.

## No longer needed

Removed the proof import `Mathlib.AlgebraicGeometry.Restrict`.
Removed proof dependency `lem-weil-pbc-open-preimage-fibre-product`: its
`isPullback_morphismRestrict` specialization is unnecessary because
`IsOpenImmersion.isPullback` handles the base-changed square directly.
Also removed the old direct proof dependencies
`def-weil-frobenius-substitution` and `def-weil-affine-spectrum`: the existing
`galoisMap_inverse` and `galoisMap_projections` interfaces supply the coefficient
action calculations, so this proof does not reconstruct them from field
Frobenius and Spec functoriality. Their definitions still occur in the unchanged
statement or its imported definitions; this is pruning direct proof work only.
No Sheaf modules are withdrawn. The other public imports are retained for the
existing statement. `Mathlib.AlgebraicGeometry.PullbackCarrier` is used by the
range formula. The unit record `sk-d-weil-push` has no separately realized steps,
and its Frobenius/open-square route is preserved.

## Where the brief, the DAG or earlier work was wrong

The old plan manually reconstructed model pullbacks and coefficient inverses
although the existing APIs provide an open-image criterion and explicit
coefficient inverse/projection identities. The node proof now uses these exact
interfaces, including the unrestricted theorems attached to
`def-weil-relative-frobenius-geometric-fiber` and
`def-weil-frobenius-detailed`; their packaged finite-type automorphism definitions
are not used. Both nodes have no unit. No statement defect was found.

Searches ran through `msearch.py` (LeanFinder, Loogle and grep), and local `rg`
searched the source library, Sheaf and Mathlib. The exact open-image criterion
was checked in Mathlib `OpenImmersion.lean`; the absolute iterate implementation
was read in `AbsoluteFrobenius.lean`. The current blueprint statement and Stacks
`definition-absolute-frobenius`, `lemma-frobenius-endomorphism-identity` and
`lemma-open-fibre-product` were read. No new node or search claim is added.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
