## What changed

Replaced the proof of `AlgebraicGeometry.ProEtale.qbarFiniteDescent`, preserving its full
statement. A private categorical helper descends a finite quiver by induction over its
finite set of generating arrows. The Hom clause is an application of
`finiteCoefficientDescentTwoColimit`, using its equality of rational constructibility
predicates to keep the underlying complexes unchanged. Relations follow from naturality
and the existing faithfulness theorem for derived extension to the algebraic closure.
The six-functor clause restricts the canonical ambient pullback comparison and the composite
of proper direct-image coefficient change with open-extension coefficient change.

The private scalar-comparison helpers keep the large derived-functor constructions
locally irreducible while checking the proof. Generic compatibility lemmas and direct
parameter application avoid expansion of local functor aliases. This avoids expensive
unfolding without changing a library definition or its interface.

The node proof, proof dependencies and proof origin record this implementation.
No existing definition, statement, visibility or public import is changed.

## Proved and sorry left

Closed the sole original hole, `AlgebraicGeometry.ProEtale.qbarFiniteDescent`
(`det-sp-qbar-finite-descent`): shifted Hom descent, finite diagrams with relations,
and both scalar comparisons. Holes closed: 1. Holes added: 0. Holes left: 0.
No split-off statements are introduced. The complete module compiled in 39.2 seconds
on the project server. Profiling options used for the timing diagnosis were removed
before delivery; the delivery tool compiles and checks the final file again.

## No longer needed

The direct proof does not use `lem-weil-pbc-filtered-colimit-sets-elementwise`: the Hom
representative/equality conditions are already supplied by the two-colimit theorem,
and faithfulness proves the finite diagram relations. It also does not use
`det-prop-scalar-six-pullback`, `det-prop-scalar-six-compact-support`, or
`det-prop-scalar-six-direct-image`. For the particular finite-to-closure inclusion,
`derivedPullIso`, `derivedOpenImmersionShriekIso` and
`isIso_derivedPushHom_padicAlgCl_of_boundedBelow` supply the exact comparison directly.
Removed proof imports: `Sheaf.SixFunctors.ScalarSixPullback` and
`Mathlib.CategoryTheory.Limits.Types.Filtered`. The generic scalar-six coherence data are
unnecessary for the existence of the natural isomorphisms asserted here. These nodes and modules are not withdrawn; other consumers
may still need them. The unit's finite-descent and proper/open route is preserved. The two new theorem
dependencies, `lem-weil-pbc-condensed-coefficient-derived-faithful` and
`lem-sfb-qlbar-direct-image-comparison`, are already proved; they specialize the required
relation reflection and proper coefficient comparison without generic coherence data.

## Where the brief, the DAG or earlier work was wrong

The planned extra enlargement to impose relations is unnecessary for these coefficient
functors: derived extension to the closure is already faithful. The blueprint argument
remains valid; the existing stronger interface shortens its relation step.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
