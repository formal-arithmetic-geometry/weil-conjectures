## What changed

Proved `AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap_range_eq_stabilizer_range`
in `Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizerRange`, preserving its full
statement and visibility. The Lean proof implements all three steps of the existing node
`lem-galois-pi1-finite-etale-image-stabilizer-range` without new intermediate obligations.

For the forward inclusion, the unique point in the fibre of the identity cover is fixed;
naturality along the diagonal and `fundamentalGroupMap_smul` give the marked-point equality.
For the reverse inclusion, compose each cover with `f`, embed its fibre over `s` into its
fibre over `s ≫ f`, and use naturality of the projection to prove preservation by a
stabilizer element and its inverse. The resulting permutations are natural, so
`toAut_bijective` supplies an element of `GX`. Naturality along the first pullback
projection and the action formula identify its image with the original element of `GY`.
Every constructed object and permutation has explicit data and proved laws.

Read SGA 1, Exposé V, Proposition 6.13 and §7 in the supplied PDF. The proposition states
the slice-fibre description and stabilizer identification, leaving its proof to the
reader; this delivery supplies that proof for finite étale schemes. The existing DAG
route remains unchanged. LeanFinder returned related generic Galois-category results,
including `fiberIsoQuotientStabilizer`, but no shorter exact theorem; Loogle located
`toAut_hom_app_apply`; the remote grep for a fundamental-group-map/stabilizer theorem
returned no match. Local searches also checked the existing fundamental-group API.

The final single-file compile through `lcompile.py` passed without warnings in 5.1 seconds.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap_range_eq_stabilizer_range`
(node `lem-galois-pi1-finite-etale-image-stabilizer-range`).

Original holes: 1. Remaining holes in the item: 0. Holes added: 0. Split off: 0.
There are no new modules or declarations with postponed proofs.

## No longer needed

Removed these four proof imports:

- `Sheaf.AlgebraicGeometry.GaloisCategories`;
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`;
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality`;
- `WeilConjectures.AlgebraicGeometry.GaloisCategories`.

The finite étale and functoriality APIs are already public dependencies of the retained
`WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction` import. The two
GaloisCategories imports concern the sheaf-category interface, which the proof does not
use. No comparison with finite locally constant sheaves is needed. These are import
removals, not a claim that the corresponding modules become unreachable from every
target. No planned mathematical step is bypassed and no existing node is withdrawn.
The finite/étale composition leaves are used through their Mathlib instances.

## Where the brief, the DAG or earlier work was wrong

No mathematical or signature correction was needed. The four proof imports above were
redundant for this finite étale argument. No definition, statement, consumer, or unit
route was changed, and no change record is required.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
