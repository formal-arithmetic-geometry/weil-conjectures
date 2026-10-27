## What changed

Filled all three proof bodies in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas`, preserving every existing
public declaration, signature, public import, and docstring. No shared module changed.

`exists_finite_affine_subatlas` uses Mathlib's finite-subcover theorem on the open images
of the prescribed affine components. Their finite open union is compact by
`IsAffineOpen.isCompact` and `Set.Finite.isCompact_biUnion`. Its inclusion remains étale;
the existing representable point-surjectivity criterion proves scheme-test surjectivity.
The proof includes empty index sets and empty point spaces without choosing a point.
Pairwise disjointness is retained as a hypothesis, although finite-union compactness
works without it.

Added proved private helpers for residue-field naturality of `schemePointMap`,
scheme-test surjectivity implying surjectivity on scheme points, continuity in the
final topology, openness, Yoneda transport of étaleness, and the scheme-source
point-surjectivity criterion. The first four reuse the already proved arguments in
`AlgebraicSpaceFlatLfpUniversallyOpen`; the Yoneda helper reuses the argument in
`AlgebraicSpace`. They introduce no new obligations.

Added private proof imports of `AlgebraicSpaceAffineEtaleCover` for openness,
`AlgebraicSpacePointOpenCalculus` for the surjectivity criterion, and
`EnlargedEtaleRingedSite` for the existing `schemeSpace` construction. The latter is
owned by `def-trf-scheme-algebraic-space`; it is only used to apply the criterion to a
representable source. Updated the item's proof steps and dependency list accordingly.
These are tool uses for the local point-topology argument; no unit or chapter route
is replaced. The unit record's realized lists do not attach this node to a unit step.

The two compactness consequences apply Mathlib `Function.Surjective.compactSpace`.
The scheme-atlas consequence derives continuity directly from the final topology and
surjectivity by the residue-field helper.

Searches used the required leanfinder, loogle and grep wrappers plus `rg` across
Mathlib, `WeilConjectures`, and `Sheaf`. Loogle found the exact generic compactness
lemma; local search found the proved scheme-point helpers and the existing scheme-space
construction. The source argument was checked in `spaces-properties.tex`, Tags 03E4
and 03FX, and the current blueprint unit was read.

Validation: the final single-file `lcompile.py` run compiled cleanly, with no warnings,
in 4.9 seconds. A source comparison checked unchanged theorem signatures, public imports
and original docstrings; all Lean lines are at most 100 characters.

## Proved and sorry left

Original holes closed: 3 of 3, all owned by
`lem-a1-space-finite-affine-subatlas`:

- `AlgebraicGeometry.AlgebraicSpace.exists_finite_affine_subatlas`.
- `AlgebraicGeometry.AlgebraicSpace.compactSpace_points_of_surjective`.
- `AlgebraicGeometry.AlgebraicSpace.compactSpace_points_of_scheme_atlas`.

Holes added: 0. Split-off statements: 0. Holes left in delivered Lean files: 0.
The proofs use the already stated atlas and point-calculus dependencies as intended by
stage 3; this delivery does not claim those dependency theorems are sorry-free.

## No longer needed

Removed the unused private import
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.

The revised proof does not use `lem-weil-pbc-open-immersion-base-change` or
`lem-a1-etale-open-restriction` directly. It proves étaleness of an open inclusion
using the existing Mathlib open-immersion instance, transports it through Yoneda,
and composes with the atlas. Those two Mathlib leaf edges were removed from this
node's proof dependencies. No project module or public declaration is withdrawn.
All other original dependency roles are retained. No new nodes were introduced.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The original point-open-calculus declaration is
formulated for morphisms between algebraic spaces, whereas the item starts with a
Yoneda scheme-source map. The proof supplies that source using the already published
`schemeSpace`, rather than assuming the criterion can be applied without this bridge.
The original separate open-restriction argument is unnecessary with the existing
Yoneda étaleness and composition construction. Existing docstrings and all statements
are preserved.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
