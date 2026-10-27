## What changed

Proved both original theorems, with unchanged signatures, in
`Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization`.
The intertwining statement is the existing `Realizations.coherence` field. Equality of
system routes is proved by induction: vertical/horizontal are the properOpen fields,
three-cell interchange is naturality, and every context case is functoriality. The four
projection-generating equations are isolated in `ProjectionSystemCoherence`. Applying total
limit preserves the system equality; the two intertwining equations then give equality of
integral maps by cancelling the invertible source comparison. The pentagon combines the
five `CanonicalPair` edges and applies that result.

Proved the coefficient two-term resolution directly: the uniformizer generates the nonzero
maximal ideal, so it is nonzero, its powers act injectively in the coefficient domain, and
the quotient kernel is its principal power ideal. This argument works also at n=0.

Moved the five data definitions and `ProjectionCoherenceRoutes` unchanged into the new
module, publicly reexported by the item, to avoid an import cycle. Checked byte identity
of both original theorem signatures and of the moved signatures/data bodies. No source
library or other group's files changed. The change record documents all consumer checks.

## Proved and sorry left

Closed the two original holes:

- `WeilConjectures.IntegralSystemRealization.projectionIntegralCoherenceRealization`.
- `WeilConjectures.IntegralSystemRealization.projectionIntegralAssociativityPentagon`.

Added one named hole:

- `WeilConjectures.IntegralSystemRealization.projectionSystemGeneratingEquations`, node
  `lem-sf-projection-system-generating-equations`, in the new module. Its four clauses are
  composition, proper/open projection compatibility, directed refinement, and normalized
  identity. Its proof is exactly `:= by sorry`, with a source and complete proof in words.

The item itself has zero holes. This is a decomposition of the system-generating part,
with the complete context induction, realization transport, coefficient resolution and
pentagon combination proved here. Two holes closed and one added; net one hole closed.
No claim that the generating system equations have been proved in Lean is made.
Both modules compiled together before the final private-helper relocation; final compile
and the delivery preflight verify the final packet.

## No longer needed

Removed private imports:

- `Sheaf.SixFunctors.ProperOpenProjectionMate`.
- `Sheaf.SixFunctors.AmbientProperOpenPasting`.
The original private `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison` import
is retained because preflight identifies it as a unit-route module, although the proof
needs no second construction of the comparison.

Removed redundant public imports from the item, which now publicly imports only
`ProjectionSystemCoherence`, `Mathlib.Algebra.Exact.Basic`, and the retained unit-route
imports `FiniteFieldFiber`, `FiniteTorAmplitudeSites`, and `CoefficientExtensionFinite`:
`IntegralCompactificationSystemRealization`, `SfIntegralConstructible`,
`SixFunctorOperationDatum`, `ExchangeProjectionSuppliedDomains`,
`QcqsCompactSupportRealization`, and `CoefDerivedSystemEvaluationCalculus`
(the latter names are under their original Sheaf topics).
All needed public interfaces arrive through the new module's public import of
`IntegralCompactificationSystemRealization`. The single import change preserves the original
theorem and data signatures; there are no external current consumers.

The original direct proof dependencies `lem-sf-projection-compatible-triangle-assembly`,
`lem-sf-proper-open-projection-mate`, `lem-sf-projection-refinement-descent`,
`lem-sf-ambient-proper-open-pasting`, and `lem-sf-three-cell-compositor` are not imported or
applied by this proof. The first three do not fit the unrestricted scheme scope of the
constructors; pasting is already in rho.properOpen, and three-cell is direct naturality.
Their mathematical system arguments motivate the new generating-equations lemma, which
states the exact missing scope. `def-exchange-projection` is not a direct proof dependency:
its specified maps are already defined by the imported realization interface.

The extra direct-image/limit theorem `lem-weil-ringed-tower-pushforward-limit-comparison`
is not needed here because the comparison is already fixed by Realizations. Its unit-route import and approved tool_uses entry are retained; no direct proof use
is asserted. No declaration/module is withdrawn, no upstream
consumer proof is removed, and no global unreachability of these modules is asserted.
The unit's route is retained; no UNIT statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The system clauses cited by the original plan are on finite-type schemes over D.k
(`Spaces D`, or explicit LocallyOfFiniteType/QuasiCompact structure-map instances).
The route constructors instead quantify over arbitrary `Over (Spec D.k)` objects.
A direct application of properOpenProjectionMateSystems fails to synthesize
LocallyOfFiniteType of the structure map; composition and refinement have the same gap.
No such instance can be inferred for an arbitrary Over object. No hypothesis was added
and no existing constructor or theorem was weakened to hide this discrepancy.

The new theorem states the four intrinsic ringed-diagram equations at the actual required
scope; their geometric tensor/unit/counit argument has no finite-type requirement.
The existing realization datum already provides arbitrary CanonicalPair intertwining,
so it is unnecessary to reprove that large assembly. The pentagon theorem accepts its
route witness: its Lean proof composes canonical pairs and uses equality of that route,
rather than rebuilding a five-compactification geometric diagram.

Checked the new statement on identity maps, zero inputs and empty opens. The clopen
projector is identity/zero and its tensor square includes the empty-open case. The
refinement clause inverts precisely the two supplied Gamma components; no projection
map or raw composition arrow is inverted. Both identity comparisons retain the bridge
normalization. No faithfulness of evaluation is assumed.

## New nodes

`lem-sf-projection-system-generating-equations`: the four explicit system projection
equations strictly below the integral-realization theorem; no integral expressions,
CanonicalPair realizations, coefficient resolution, route/context induction or pentagon
is deferred to this node. The proof uses the general mixed tensor-square/mate argument
and the normalized simultaneous system operations. The existing finite-type clauses
were inspected and found insufficient at the required scope. Three actual search kinds
are recorded, and blueprint_refs found no matching blueprint node. The new node and the
updated item node record the Lean proof route. Data relocation record:
`coord/changes/projection-system-coherence-relocation.md`.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
