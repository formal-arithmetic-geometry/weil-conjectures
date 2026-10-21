## What changed

Repair of the no-op return at `d5ef8ca63b`, using the current live module as the
baseline. `AlgebraicGeometry.relativeMV_cover_chain_square` now assembles its
three equations by postcomposing the supplied transposition/rectification
equalities and simplifying associativity and the supplied mate equations.
This removes the initial eager `dsimp only` and both backward transparency
overrides. The existing heartbeat allowance remains necessary and is retained.

The strict square, all six comparison isomorphisms and all three equations,
including the fixed overlap cone map, are preserved. The signature, universes,
visibility, docstring and imports are unchanged. No other Lean module changes.
The existing node's third proof step and proof provenance now describe the
postcomposition argument, with exactly the same three proof dependencies.
Change record: `coord/changes/B4-relative-mv-cover-chain-square-restoration.md`.

## Proved and sorry left

This is a repair of an already proved module: 0 of 0 holes closed, 0 holes added,
0 split off, 0 remaining. The declaration
`AlgebraicGeometry.relativeMV_cover_chain_square` remains completely proved.
There is no `sorry` in the delivery and no new declaration.

The exact signature was compared with both current live source and the existing
node attachment; both match. All Lean lines are at most 100 characters.
The revised proof compiles through `lcompile.py` with the existing heartbeat
allowance and without either transparency override. An attempt at the default
heartbeat budget exhausted it, so no reduction of that allowance is claimed.

A fresh validation tree compiled the revised item in 27.8 s and its unchanged
direct consumer `Sheaf.AlgebraicGeometry.RelativeMVCoverRows` in 14.3 s.
`#print axioms` for both declarations lists exactly `propext`,
`Classical.choice`, `Quot.sound`; both compiles produced no warnings.
The validation files are outside the delivery's `lean/` tree.

## No longer needed

No imports, nodes or modules are pruned. All three proof dependencies remain
used: the relative direct-image homotopy comparison, derived-pullback
cone-square transposition, and homotopy-square cone rectification.
The eager whole-goal normalization and the two transparency overrides are
removed. No generic theorem is withdrawn merely because the finite-free root
now takes another route.

LeanFinder found the Mathlib cone/homotopy operations; Loogle found the cone map,
its composition laws and its identification with `mapOfHomotopy`. None supplies
the specified relative geometric comparison. The three-step route is retained.

## Where the brief, the DAG or earlier work was wrong

The previous packet described a missing-source restoration, but that exact
source has since been restored independently. Repeating it would reproduce the
returned no-op. This packet makes an actual proof change in the current live
module and removes the now-unnecessary elaboration overrides.

The route note's proper-flat finite-free replacement is already integrated in
`WeilConjectures.AlgebraicGeometry.ProperFlatCechModel`, which invokes the
upstream descent-first construction. The generic row theorem is also now
proved from `relativeMV_direct_image_rows_core`. Neither development is
redelivered or claimed as this session's work. The independently used generic
chain-square statement and its consumer remain in the library. No target,
source-library interface or unit route changes.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
