## What changed

Added `Sheaf.AlgebraicGeometry.GenericGeometricallyReducedAffineModel` as a strict intermediate theorem and proved the item theorem from it by uniqueness of generic points on an integral scheme. The item module now imports only that intermediate module and the public Mathlib declarations needed by its statement.

## Proved and sorry left

The item declaration `AlgebraicGeometry.exists_generic_geometricallyReduced_preparation` is proved. One strictly smaller construction theorem remains sorry: `AlgebraicGeometry.exists_generic_geometricallyReduced_affine_model` (node `lem-pur-generic-geometrically-reduced-preparation-core`).

## No longer needed

The item proof does not use the originally listed low-level ring construction modules directly; their route is encapsulated by the new affine-model theorem. No existing node is claimed pruned because the unit route remains represented by the intermediate node.

## Where the brief, the DAG or earlier work was wrong

The original item proof plan combines substantial affine ring construction, reduction/fibre comparison, and three generic shrinking arguments in one theorem. The proof was reduced to a named intermediate theorem strictly below the target; the target itself is then a short generic-point uniqueness argument.

## New nodes

`lem-pur-generic-geometrically-reduced-preparation-core` records the affine construction and shrinking argument, with its source and dependencies.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
