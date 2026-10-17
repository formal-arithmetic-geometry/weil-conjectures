## What changed

Repaired the assigned 60-second compile failure in
`WeilConjectures.PoincareDuality.Poincare` by adding module-local irreducibility
attributes for the expensive derived closed structure, coefficient module closed
structure, and pro-étale upper-star implementation. A local instance priority
attribute keeps the bounded-constructible subcategory instance selected during
elaboration. These controls prevent kernel conversion from unfolding the
K-injective internal-Hom and coefficient pullback implementations.

Only the item module changed. Its public imports, declarations, signatures,
definitions, theorem statements, and proof bodies are unchanged. The repaired
module compiles in about 22 seconds, below the 60-second limit. No upstream module or public declaration was changed, so no forced adaptation
is needed. The local attribute change is recorded in
`coord/changes/B3-poincare-local-reducibility.md`.

## Proved and sorry left

This is the listed red-build definition repair. Holes closed: 0 of the item's 1.
Holes added: 0. Split-offs: 0.

The existing hole in the item is unchanged:
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tateTwistDerived`
(node `nt-target-poincare-tate-bc`). No definition contains `sorry`.

## No longer needed

No mathematical dependency, import, node, or module is pruned. The earlier
upstream exposure-repair experiment is withdrawn because the item-local controls
alone bring compilation under the limit and preserve the existing library
interfaces.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt changed an upstream definition to `@[no_expose]`, which the
static stage-3 gate rejects as an upstream attribute/body change. The assigned
repair can be completed within the item module: local irreducibility prevents the
same expensive unfolding without changing any upstream declaration or consumer.

## Forced adaptations

None. The delivery changes only the item module and leaves all other modules
untouched.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
