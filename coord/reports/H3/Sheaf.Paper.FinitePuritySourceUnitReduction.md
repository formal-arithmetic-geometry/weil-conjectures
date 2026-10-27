## What changed

Filled `AlgebraicGeometry.Scheme.PurityIntegralTower.finitePuritySourceUnitReduction`
without changing its statement or any definition. Added six proved private helpers.
`transportScalarSource` performs the origin-adjunction cancellation in arbitrary
categories; `tensorBalancing` packages ordinary balancing naturally;
`tensorBalancing_unit` reduces that balancing at the coefficient unit to the line
comparison. `comparisonCounitUnitIsIso` proves invertibility of the comparison counit on
the coefficient unit; `finishSourceTransport` cancels the remaining target-unit
coordinates.
`finishUnitSquare` combines transport and unit coherence by naturality. The final
proof combines these for the actual finite quotient maps and the specified
unitSource/unitReduction. The private helpers keep derived-functor elaboration within the existing
per-declaration heartbeat budget.

Added proof imports of FiniteSmoothLevelOfOrientation (import all, for its proved
private sourceNatIso/sourceNatIso_app and ordinaryUnitCtf helpers),
EtaleScalarPullbackUnitCoherence (import all, also reusing its proved generic
tensor_naturality_left helper), and ExceptionalCoefficientLeftUnitCoherence.
Updated the item's DAG proof to this argument. No shared module was edited.
The two unit-coherence lemmas are generic tools;
using them does not replace a step of the blueprint unit route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.PurityIntegralTower.finitePuritySourceUnitReduction`
(node `lem-pur-finite-source-unit-reduction`). Added zero holes and zero split-off
statements. Every new private helper is fully proved. No sorry remains in the item.
The proof uses the existing library's coherence results; their dependencies retain
their own existing proof obligations.

## No longer needed

No original Lean import was removed; no module or declaration is withdrawn.
The node's direct representative-level dependency on
`lem-pur-derived-change-of-rings` and its direct dependency on
`def-pur-etale-scalar-pullback-iso` are replaced by the existing, more specific
`lem-pur-scalar-left-unit` and
`lem-pur-etale-scalar-pullback-unit-coherence`. The underlying scalar and pullback
constructions are still needed transitively. No global pruning is claimed.
No new K-flat representative calculation, root-generator calculation, or induction
on tensor powers is needed here: the argument works for an arbitrary line
isomorphism, instantiated with the already specified `r.tensorPower d`.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically compatible with this proof, but its ordinary
representative calculation is already available through the two unit-coherence
lemmas. The current item is present in lean/ despite an older quarantine/rework row;
its complete declaration and Lean attachment are preserved. The proof adds no
Noetherian, smoothness, orientation, strict-level, or positive-degree assumption.
The arbitrary-line unit calculation includes d=0; the categorical argument includes
identity quotient maps and never divides by a degree or cancels a non-isomorphism.

Validation: the complete proof compiled through lcompile in 40.4 seconds with
profiling enabled. Profiling and checkpoint commands were removed before delivery.
The public signature is byte-for-byte unchanged, every Lean line is at most 100
characters, and the item contains zero sorry tokens. All proof imports are used.
Synchronous elaboration and local irreducibility annotations keep the existing
derived-functor definitions abstract during elaboration; no shared attribute or
definition is changed.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
