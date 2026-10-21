## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleRingedExtensionByZero_products` in
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts`, following all five steps of
`lem-cbc-ringed-open-extension-products`. The reduced induced closed complement supplies the
recollement theorem. The invertible open adjunction unit identifies the open image of the
canonical comparison with a product of isomorphisms. Closed restriction preserves products
and annihilates extension by zero, so its image is an isomorphism between zero objects.
The localization sequence detects zero objects; a proved private helper applies this to the
kernel and cokernel using exactness of the two restrictions. Naturality is proved by
composition with every product projection.

Added private proof imports of Mathlib's preservation APIs for kernels, cokernels and products.
The existing public imports and theorem signature are unchanged. No other module is adapted.
The proof follows Stacks `proetale.tex`, Tag 09BP (`lemma-j-shriek-limits`), with the ringed
recollement refinement already specified in the node. No ambient compactness is used.

Validation: remote single-file compilation passed without errors or warnings (10.9 seconds).
The arbitrary index type is unchanged; the zero-product argument uses product extensionality
and therefore includes the empty family. Empty opens, the identity open, empty schemes and
the zero coefficient ring require no extra assumptions or case exclusions.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.proEtaleRingedExtensionByZero_products`
(node `lem-cbc-ringed-open-extension-products`).

Added 0 holes. No `sorry` remains in the delivered module. The private theorem
`AlgebraicGeometry.Scheme.jointly_detect_iso` is also fully proved. No new statement is split off.

## No longer needed

None. Both original proof imports are used, and every declared proof dependency is retained:
the reduced closed complement, ringed recollement, immersion inverse-image preservation,
sectionwise module limits and the abelian module category. No node or module is withdrawn.
The open product-preservation instance is obtained directly from the recollement adjunction;
the immersion theorem supplies exactness of open restriction and product preservation and
exactness of closed restriction. This is the same open/closed detection route as the node.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing declarations supply every step of the
plan. There are no new nodes, definition repairs, consumer adaptations or change records.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
