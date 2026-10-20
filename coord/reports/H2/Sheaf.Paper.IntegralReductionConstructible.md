## What changed

Restored the complete assigned module from
`quarantine/Sheaf/Paper/IntegralReductionConstructible.lean` without withdrawing it.
Added a proof-only import of the relocated
`Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.
Installed the three projections of `integralConstructible_serre` as explicitly typed
local instances, and explicitly selected the proved
`isTriangulated_boundedConstructible_of_serre` instance before applying the existing
mapping-cone argument. All public theorem signatures, existing constructions, public
imports, and the quotient restriction/finite-presentation proofs are unchanged.

The restored module compiles without errors or warnings (about four seconds).
A separate consumer imports only this module, opens the standard scoped object
instances, installs the same explicit Profinite size instance as the existing quarantined consumer, and applies the theorem with its
unchanged full statement. The consumer compiles. The axiom probe still reports
`sorryAx` inherited from pre-existing dependency proofs; no hole is introduced here.
The only direct importing consumer is the quarantined
`Sheaf.Paper.IntegralResidueExchange`; it already installs that same size instance,
and its application at line 124 keeps the identical signature. No adaptation is needed.

Updated the existing node's proof and proof dependencies to name the proved weak
Serre triangulated-closure theorem explicitly. The unit route is unchanged.
Change record: `coord/changes/H2-integral-reduction-constructible-restore.md`.

## Proved and sorry left

This is a zero-hole rework repair: 0 existing sorries, 0 closed, 0 added, and 0 split off.
The complete proof of
`AlgebraicGeometry.ProEtale.CondensedRing.integralReduction_boundedConstructible`
is restored and repaired. Every private helper remains fully proved.
There are no remaining sorries in the delivered module and none added elsewhere.
No claim is made to have closed the pre-existing holes in imported dependencies.

## No longer needed

No imports, modules, or nodes are pruned. All three original declared proof
dependencies are retained and used. The proof explicitly uses the integral weak
Serre route rather than selecting the upstream noetherian-only triangulated
instance restored by synchronization.

## Where the brief, the DAG or earlier work was wrong

The item is absent from `lean/` because it was quarantined after upstream sync,
not because its mathematics was withdrawn. Its archived proof already has zero holes.
The recorded `obtain`/`generalize` failure is a missing proof-context visibility
problem for the closure predicates. Importing their relocated proved API repairs it.
With only the predicates imported, instance synthesis also selected the upstream
noetherian-only triangulated instance, rendering the integral Serre hypotheses
unused. Explicitly selecting the proved Serre-based instance preserves the intended
argument and uses the finite-dimensional coefficient hypothesis.
The node's old proof-origin note incorrectly mentioned an outstanding coefficient
comparison theorem; this module's retained proof has no such local hole.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
