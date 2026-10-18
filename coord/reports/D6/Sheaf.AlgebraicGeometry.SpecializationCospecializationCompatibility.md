## What changed

Proved AlgebraicGeometry.Etale.specialization_cospecialization_compatibility from a strict-local factorization and a derived restriction naturality/cancellation calculation. Added support module Sheaf.AlgebraicGeometry.StrictBaseFibreMapFactorization and imported it privately.

## Proved and sorry left

The item theorem is proved. The support theorem AlgebraicGeometry.Etale.strictBaseSheafFiberMap_factorization remains as one named split with a Stacks Tag 0GJV proof plan; it is the only remaining sorry.

## No longer needed

Removed proof-only imports of strict-local germ/base-change modules, derived exchange termwise modules, K-injective helpers, germ/exchange modules, and strict-henselization auxiliary modules from the item. The support module retains the needed route imports.

## Where the brief, the DAG or earlier work was wrong

The original item proof plan omitted a standalone Lean interface for the strict-local comparison identifying both fibre composites. This was split into the strictly smaller factorization theorem above.

## New nodes

lem-weil-pbc-strict-base-fibre-map-factorization in dag/nodes/sec-proper-base-change records the remaining factorization theorem and its source, dependencies, and proof route.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
