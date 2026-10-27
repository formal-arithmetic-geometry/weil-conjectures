## What changed

Proved `AlgebraicGeometry.meromorphicSheaf_generic_product` in
`Sheaf.AlgebraicGeometry.MeromorphicSheafGenericProduct`, preserving its complete signature.
Added proved private helpers for generic-point topology, localization and sheafification on
stalks, evaluation of products, and compatibility with scalar multiplication. The stalk
identifications invert the canonical localization maps. Multiplication is the unique section
with the pointwise product of generic coordinates; denominator cancellation proves its
fraction formula. Restriction compatibility follows from the germ identities and section
injectivity. Updated the existing node's proof and proof origin to match this argument.

Added private proof imports of ProjectionFormula (invertible implies quasi-coherent),
Sheafify (sheafification preserves stalks), and MinimalPrime.Localization (regular elements
avoid minimal primes). No public import, statement, or definition interface changed.
The complete file compiled on the project compile server in 42.5 seconds before removing
two redundant imports; the delivery performs the final compile and preflight.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.meromorphicSheaf_generic_product`
(node `lem-sc-meromorphic-sheaf-generic-product`).
There are zero remaining holes in this module and zero holes added elsewhere.
No statements were split off. All added private helpers have complete proofs.
The proof uses the existing declarations
`Scheme.associatedPoints_eq_weaklyAssociatedPoints` and
`meromorphicModule_generic_product`; their remaining proof obligations are unchanged.

## No longer needed

Removed the redundant private import
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`, already publicly imported by
`MeromorphicModule`. The attempted KrullDimension.Zero proof import is also absent:
regular elements avoid the unique minimal prime, so no Artinian-ring argument is needed.
The tensor-stalk argument and `meromorphicModule_tensor_iso` are not used: the canonical
localization map is directly bijective on generic stalks for every module.
All existing node proof dependencies remain used (including invertibility for
quasi-coherence and the module-stalk scalar action). No module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was needed. The DAG's Artinian-ring and
tensor-stalk calculations were longer than necessary. The updated proof records the
direct localization argument and the fraction-cancellation construction instead.
Empty opens and generic points outside an open are handled by unique sections over
empty inverse images; no quasi-compactness assumption is added to the section bijections.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
