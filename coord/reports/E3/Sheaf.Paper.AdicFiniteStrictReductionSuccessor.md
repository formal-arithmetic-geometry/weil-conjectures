## What changed

Filled `AlgebraicGeometry.Scheme.adicFiniteStrictReduction_successor` in
`Sheaf.Paper.AdicFiniteStrictReductionSuccessor` without changing any public signature,
definition, or public import. Added private proof imports of
`Sheaf.Paper.AdicNormalizedScalarComposition` and
`Sheaf.Paper.ConstantCompletionEquivalence` to reuse their proved scalar calculations.
Two proved private helpers identify the ordinary quotient successor and transport the
normalized scalar comparison to the specified composite and arbitrary presentation `e`.
The node proof and dependencies now describe this route.
The complete proof compiled on the server in 53.3 seconds with profiling enabled;
profiling options were then removed for delivery. The ordinary and derived comparison
helpers are complete, and normalization unfolds only local aliases and the specified
transition, without changing any shared definition or relaxing transparency settings.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.adicFiniteStrictReduction_successor`
(node `lem-sfb-adic-finite-strict-reduction-successor`).
No holes added or split off. No `sorry` remains in the item module.

## No longer needed

No existing imports removed and no modules withdrawn. The direct planned dependency
`lem-pur-kflat-change-of-rings` (`Sheaf.Algebra.Homology.ChangeOfRingsKFlat`) is unnecessary
here: the proved scalar comparison already supplies the K-flat base-change calculation
using its independent-coefficient version. This is a removal of a direct proof dependency,
not a claim that all K-flat change-of-rings theory is absent transitively.
The existing reduction-data and constant-completion nodes remain needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement repair. The shorter existing route is in
`AdicNormalizedScalarComposition`: its private, fully proved
`scalar_transition_comparison` and `canonical_step_naturality` calculations apply to
arbitrary ring-sheaf maps and therefore to these constant-coefficient quotient maps.
The earlier search noted a different completed-coefficient successor but did not use
these generic calculations. No unit-level route changes.
The proof works uniformly for zero and unit ideals, zero complexes and empty schemes;
none of the specialization or transport steps assumes nontriviality.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
