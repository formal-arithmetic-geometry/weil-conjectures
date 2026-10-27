## What changed

Filled `AlgebraicGeometry.ProEtale.SpTowerClasses.exists_integralUnitReduction`
without changing its statement or any existing public imports. Its proof imports
`IntegralTowerScalarPresentation`, `ResolvingAdjunction`,
`DerivedChangeOfRingsCochainModel`, `KFlatResolutionIndependentCoefficients`, and
`FlatSingleDerivedNormalization` privately.

The new module `Sheaf.Paper.IntegralTowerScalarPresentation` proves the ordinary
integer-module presentation, the exact forgetful functor with the four required
literal section equations, and the normalized ordinary tensor-unit adjunct.
Its integer ring, integer scalar map, equivalence, forgetful functor and comparison
are actual constructions. No arbitrary data are selected from a holed existence
statement. Its only public theorem is
`AlgebraicGeometry.ProEtale.SpTowerClasses.exists_integralTowerScalarPresentation`.

A private generic lemma transports K-flat resolutions along the exact cochain equivalence,
applies the existing resolving-class derived-adjunction theorem, and retains the prescribed ordinary adjunction. A second private lemma proves the
single-complex transpose formula. Flatness of the ordinary unit makes the actual
integer single complex a resolving object. This gives the requested isomorphism
and its equality with precisely `integerGenerator`.

Both modules were checked with the server compiler. The final generic transport
proof compiled in 35.4 seconds with profiling enabled; profiling options have
been removed for delivery.

Only the assigned existing module and its node, and the new proved helper module
and its node, are changed. No shared definition, source-library declaration, target
statement, instance or public import of an existing module is changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.SpTowerClasses.exists_integralUnitReduction`
(node `lem-sfb-integral-unit-reduction`).

Also proved the new ordinary helper
`AlgebraicGeometry.ProEtale.SpTowerClasses.exists_integralTowerScalarPresentation`
(node `lem-sfb-integral-tower-scalar-presentation`). It has no `sorry`.

Original holes: 1. Closed: 1. Holes added: 0. Holes left in this delivery: 0.
No obligation is split off with an unproved statement.

## No longer needed

No original import is removed, and no module is withdrawn.
The original plan's direct applications of
`lem-cbc-constant-ring-module-sheaves` and `lem-pur-system-scalar-model` are replaced
by the proved literal constant-sequence equivalence, the integer-forgetting
equivalence, the normalized ordinary tensor adjunction, and the resolving-class
derived-adjunction theorem. The original node's proof dependencies are updated.
Both old modules remain transitively imported by existing library modules, so this
delivery claims no pruning of either module or its dependencies. Pruned: none.
The unit's integral-reduction route is retained.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was required. The DAG plan omitted the
ordinary equivalence and the single-complex normalization glue. These are now
proved explicitly. The generic resolving-class theorem supplies the derived
adjunction and its representative transpose equation directly, so a new holed
version of the derived extension theorem is unnecessary.
The constructions and proofs impose no nonzero-ring or nonempty-site hypothesis;
zero coefficient rings and the empty scheme remain covered.

## New nodes

`lem-sfb-integral-tower-scalar-presentation` records the proved ordinary part of
the argument. Its module constructs the constant sequence integer ring and scalar
map and proves the equivalence, exact forgetful realization, source-unit comparison
and ordinary generator normalization. It asserts no derived existence or derived
adjunction and is strictly the ordinary part of the assigned integral reduction.
No change record is needed because no existing statement or definition changes.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
