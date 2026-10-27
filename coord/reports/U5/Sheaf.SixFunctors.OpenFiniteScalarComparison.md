## What changed

Proved `WeilConjectures.OpenSemilinearTensor.existsUnique_openFiniteScalarComparison`.
At each finite level the proof specializes the existing coefficient-linear slice comparison
to a constant coefficient tower, then transports it through the supplied completed and finite
coefficient equivalences using the normalized scalar adjunctions. It proves the required
generator equation explicitly. Two successive adjunction Hom equivalences show that those
generators determine a morphism; this gives both naturality and uniqueness.

The new proved module `Sheaf.SixFunctors.OpenFiniteScalarUnitTransport` isolates the
unit-preserving comparison across the coefficient equivalences. Its scalar-restriction
square is constructed by identity maps on sections; their linearity is exactly the
projection equation. The item imports this helper and `SemilinearSliceScalarGenerators`
privately. Its public statement and public imports are unchanged. All other helpers are
private and proved. No existing definitions or consumers change.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.OpenSemilinearTensor.existsUnique_openFiniteScalarComparison`
(node `lem-sf-open-finite-scalar-comparison`).

Also proved `WeilConjectures.OpenSemilinearTensor.exists_openFiniteScalarUnitTransport`
(node `lem-sf-open-finite-scalar-unit-transport`).

Holes added: zero. Holes left in both delivered modules: zero. The proof uses the existing
`SheafOfModules.exists_semilinearSliceScalarGenerators` declaration, whose remaining proof
obligations belong to its existing dependency modules; none is duplicated or split here.

## No longer needed

No original mathematical dependency or public import is removed. The direct proof import
of `EquivalenceAdjunctionComparison` moves from the item to the proved transport helper.
No module is withdrawn. Only one
coefficient-linear component and its generator formula from the generic slice comparison
are needed; its strict-system transition and chain comparison fields are not used here.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The supplied equivalences need not be literally the identity:
the proof retains their prescribed forward-functor equalities, including the section casts,
and uses `o.projections n` to construct the scalar-restriction square. The updated DAG spells
out the normalized scalar-model and adjunction-transport declarations used for that step.
The empty-open and zero-module cases need no separate hypothesis: the adjunction argument
and generic slice comparison apply to them unchanged.

The combined proof initially compiled without errors in 88 seconds. After profiling,
replacing the scalar-restriction compositor by explicit identity maps, isolating unit
transport, and making the private comparison definitions irreducible behind their section
formula, the combined file was still over 60 seconds. Following the worker brief's §3a,
the self-contained, fully proved unit transport is now a separate module. No unresolved
statement was extracted and no compilation limit was raised.

## New nodes

`lem-sf-open-finite-scalar-unit-transport` in
`dag/nodes/sec-six-functors/lem-sf-open-finite-scalar-unit-transport.json` records the
unit-preserving scalar-adjunction comparison across the supplied integral and finite
coefficient equivalences. It is fully proved in
`lean/Sheaf/SixFunctors/OpenFiniteScalarUnitTransport.lean`. It asserts neither an
extension-by-zero comparison nor its uniqueness, and is the categorical substep used by
the finite scalar generator calculation. There is no change record: no existing shared
interface changes.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
