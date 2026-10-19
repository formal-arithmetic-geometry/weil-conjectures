## What changed

Filled the four theorem proofs in `Sheaf.Paper.CommonStageConstituentNonexceptional`.
All declaration signatures, definitions, visibility, and existing public imports are unchanged.
Added proof-only imports for the finite-field character, dimension, pullback, and derived-category APIs.

The character coefficient is obtained by injecting multiplicative shifts of the nontrivial
trace character into all additive characters. Linear independence bounds the latter set by
the cardinality of the field, giving bijectivity and uniqueness, including the trivial character.
The affine line is irreducible and smooth of relative dimension one, hence pure of dimension one.
Density and existence of points in a scheme pullback give a geometric point of the open;
its stalk makes global sections nontrivial. Finite type and quasi-compactness give
Noetherianity, and the injective geometric-field map gives characteristic p.
Finally, the actual Artin–Schreier complex is a single object in degree zero, so its
homology vanishes in both required ranges. The same integral representative witnesses
both rational and common-stage standard classes, without a rank-one or nontrivial-character
hypothesis. Thus zero scalars and trivial characters are covered.

## Proved and sorry left

Closed all four original holes (namespace `WeilConjectures`):

- `sfFourierCharacterScale_existsUnique`.
- `sfAffineLine_curve`.
- `sfAffineOpen_geometry`.
- `sfAffineLinearArtinSchreier_mem`.

All four belong to node `def-a1-constituent-nonexceptional`.
Holes added: zero. Holes remaining in the delivered module: zero.
No intermediate theorem was split off. Existing imported results and constructions
retain their own separately tracked proof obligations.

## No longer needed

Removed the redundant trial imports `Mathlib.AlgebraicGeometry.AffineSpace` and
`Mathlib.AlgebraicGeometry.Noetherian`; their APIs are already provided by the retained
imports. No existing imports, nodes, or modules are pruned. The node has no planned proof steps or
proof dependencies to replace; its defining statement and the unit route remain unchanged.
No new intermediate theory is required: the four auxiliary obligations use existing
Mathlib and library declarations directly.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or definition required correction. The four earlier postponed
proofs can be discharged from the current APIs. In particular the heart proof only needs
the construction as a degree-zero single object, rather than redoing the finite etale
torsor argument already recorded in `fourierAdicArtinSchreier_mem`.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
