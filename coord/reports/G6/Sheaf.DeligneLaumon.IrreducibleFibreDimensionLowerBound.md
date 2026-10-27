## What changed

Proved `AlgebraicGeometry.irreducible_fibre_dimension_lower_bound` with its existing signature.
Two proved private helpers identify the fibre residue field and its scalar map. The proof uses
the stated closed-irreducible dimension/trdeg theorem, the transcendence-degree tower identity,
the irreducible locally-algebraic dimension theorem, and openness of bounded fibre dimension.
Updated the node proof and dependency list to match this argument. Added only private proof
imports of Mathlib Noetherian geometry, the transcendence-basis API, and PointCount.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.irreducible_fibre_dimension_lower_bound`
(node `lem-zl-irreducible-fibre-dimension-lower-bound`). Added 0 holes and split off 0 theorems.
No sorry remains in the delivered module. Both private helpers are proved.
The result still uses the project's stated dependencies as intended; this report does not
claim that their transitive proof dependencies are all sorry-free.

## No longer needed

Removed proof imports:
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField`.

The proof no longer needs these declared dependencies:
- `lem-kun-dimension-finite-type`: the closed-irreducible dimension theorem already supplies
  natural-number representatives for X, its image closure, and its generic fibre. The pointwise
  argument treats infinite local dimension directly, so global bounds for other fibres are unused.
- `lem-weil-pbc-fibre-product-point-residue-field`: the fibre inclusion is surjective on stalks,
  which directly proves its residue-field map bijective, compatibly with the base field.
- `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`: Mathlib directly provides the
  Noetherian-space and quasi-compact-morphism instances, without a minimal-closed-set argument.
- `def-weil-finite-type-morphism` is still a statement dependency, but its redundant proof-dependency
  entry is removed; finite-type base change is recorded by its actual permanence node instead.

These are local dependency prunings; upstream declarations and modules remain in the library.
No unit statement or realized unit step was bypassed. No top-level tool_uses entries were removed.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid but longer than necessary: its tensor residue-field calculation,
minimal-closed-set detour, and global finite-dimensionality argument can all be omitted.
The existing declaration docstring describes that original eight-step plan; the updated node
records the shorter implemented proof. The statement is unchanged, including irreducibility
without reducedness and a possibly non-dominant morphism. No consumer adaptation is needed.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
