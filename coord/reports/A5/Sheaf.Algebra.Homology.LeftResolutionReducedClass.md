## What changed

Proved `CategoryTheory.Abelian.leftResolution_reduced_class` in
`Sheaf.Algebra.Homology.LeftResolutionReducedClass`, without changing its statement.
Added the proof-only import `Mathlib.CategoryTheory.ObjectProperty.FiniteProducts`.
The proof equips the full subcategory on F with a zero object and finite coproducts,
splits its idempotents using abelian idempotent completeness and retract closure,
lifts the given cover into this subcategory, and applies `LeftResolution.reduced`.
The unused-variable linter is disabled only for this theorem because the existing
existential binders zC, fcC and zQ deliberately assert structures without later
explicit references. Their names and types are preserved.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Abelian.leftResolution_reduced_class`
(node `lem-sfb-left-resolution-reduced-class`).
No sorry remains in the delivered module. No holes or intermediate statements added.
This is a proof, not a decomposition. All dependencies used are proved in Mathlib.

## No longer needed

None. No imports removed. All three declared proof dependencies remain used:
`def-sp-abelian`, `lem-sfb-abelian-idempotent-complete`, and
`lem-sfb-left-resolution-reduced-api`. The Lean proof follows the existing two-step
DAG plan; no nodes or modules are pruned and no route change is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. Mathlib already supplies the full-subcategory
preadditive and additive-inclusion instances, finite-coproduct closure API, and
reduced left-resolution construction. The remaining packaging is now proved.
The edge cases F containing only zero objects, F containing every object, and a
cover functor P that does not preserve zero require no extra assumption: the
zero-preserving functor is the reduced resolution, not P itself.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
