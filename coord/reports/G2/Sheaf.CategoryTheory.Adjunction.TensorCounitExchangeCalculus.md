## What changed

Filled both theorem proofs in
`Sheaf.CategoryTheory.Adjunction.TensorCounitExchangeCalculus`, preserving every
existing declaration signature, definition body, and public import.

Added four proved private helpers for the monoidal image of tensoring a counit,
transport through beta, naturality of inverse projection maps, and the restricted
inverse Hom bijection. Both proofs implement the existing five-step DAG argument:
expand inverse transposes, apply mate/counit and beta naturality, use the assumed
exchange equation and monoidal unit comparison, move the unit mate through the
inverse projection, and use injectivity of the inverse Hom bijection. The restricted
proof applies counit naturality to the morphism V1 -> 1 inside the specified full
subcategory and uses no tensor closure assumption.

## Proved and sorry left

Closed the two existing holes:

- `CategoryTheory.tensorCounitExchangeCalculus`
- `CategoryTheory.tensorCounitExchangeCalculus_restricted`

Both belong to `lem-sp-tensor-counit-exchange-calculus`. No holes added or split
off. No `sorry` remains in the delivered module. The proof uses Mathlib only.
The module compiled successfully; delivery runs the final compile and axiom probe.

## No longer needed

None. All three existing public imports are required by the public statements and
definitions. All four recorded proof dependencies are used through their Mathlib
interfaces: adjunction Hom bijections, the mate counit equation, strong monoidal
functor coherence, and monoidal category functoriality. No node or module is
withdrawn, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was needed. Projection naturality for P is not
needed separately once the source transpose and the explicit exchange equation are
given; the existing hypothesis is preserved. The explicit source comparison also
means its monoidality need not be expanded in the proof. The restricted calculation
requires only counit naturality at the explicitly admitted unit-comparison endpoints.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
