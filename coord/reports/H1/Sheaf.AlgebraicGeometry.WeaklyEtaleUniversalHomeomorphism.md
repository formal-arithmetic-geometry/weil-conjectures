## What changed

Proved `AlgebraicGeometry.isIso_of_weaklyEtale_of_universalHomeomorphism` in
`Sheaf.AlgebraicGeometry.WeaklyEtaleUniversalHomeomorphism`, without changing its signature,
visibility or public imports. The proof follows the reviewed seven-step DAG argument:
universal homeomorphy gives surjectivity and universal injectivity; the underlying
homeomorphism makes the morphism affine, hence separated and quasi-compact. Its diagonal
is flat, surjective, a closed immersion, and therefore quasi-compact and monic. Its
self-pullback projection is invertible, and fpqc descent makes the diagonal invertible.
The diagonal criterion then gives monicity of the original morphism, and a second
self-pullback/descent argument proves that morphism invertible. Mathlib supplies all
auxiliary declarations, including both categorical diagonal calculations.

The source read was Stacks `more-morphisms.tex`,
`lemma-weakly-etale-universal-homeomorphism` (Tag 0F6V), together with the recorded Mathlib
signatures for all ten proof dependencies. Searches through leanfinder, loogle, and grep
found no direct theorem for this item. The unit record has no realized statement or
steps to bypass. The theorem and its existing docstring implement the same route, so no
node changes are necessary.

Validation: the final reduced import set compiled without errors or warnings through
the required remote compiler in 2.4 seconds. Delivery preflight also checks the compiled
declaration's axioms and unchanged signature.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.isIso_of_weaklyEtale_of_universalHomeomorphism`
(node `lem-trf-weakly-etale-homeomorphism`).

Zero holes remain in the item; zero holes added; zero statements split off. All proof
dependencies are proved Mathlib declarations. This is a proof, not a decomposition.

## No longer needed

Removed proof-only imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`;
- `Mathlib.AlgebraicGeometry.Morphisms.Integral`;
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed`;
- `Mathlib.AlgebraicGeometry.Limits`.

Properness, integrality, universal closedness and finite coproducts are unnecessary.
All ten declared proof dependencies are still used, with only the separated clause of
`def-weil-proper-morphism`, clauses (2)-(3) of affine permanence as applicable to
affine morphisms, and the affine clause of closed-immersion permanence. The proof
uses the scheme pullbacks already provided by its required imports. No project module
or DAG node is made unnecessary, and no new imports were introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface defect found. The reviewed DAG correctly replaces the
blueprint's explicit affine-ring calculations by the existing general fpqc descent
theorem; the Lean proof follows that reviewed argument. No change records or forced
consumer adaptations are needed.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
