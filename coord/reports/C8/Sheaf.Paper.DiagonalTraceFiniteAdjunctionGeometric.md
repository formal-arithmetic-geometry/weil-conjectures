## What changed

Corrected the false arbitrary-function interface of
`diagonalTrace_finiteAdjunction_geometric`. The new statement calculates the
geometric equation for the actual finite direct-image operation. Its proof is
complete from the coefficient-unit component and adjunction naturality.

Constructed `completedPushUnit`, `Presentation.finitePushUnit`, and
`Presentation.finitePushComparison`. The evaluation square is constructed using
the existing K-injective evaluation theorem and uniqueness of derived functors;
its existence proof is complete. No data is taken from an unproved existence
statement.

Adapted the unclaimed parent
`Sheaf.Paper.DiagonalTraceFiniteAdjunctionFactorization`: its statement is
verbatim unchanged. Its proof now chooses this actual operation and proves its
supported and geometric equations for that same witness. The supported equation
uses ordinary supported-source normalization, naturality of the derived unit,
and compatibility of normalized derived limit and finite evaluation.

The interface repair and consumer audit are recorded in
`coord/changes/C8-diagonal-finite-operation.md`. No adopted-source module,
target statement, existing definition, instance, or attribute is changed.

## Proved and sorry left

The original arbitrary-function assertion was false and is corrected, not
claimed as a proved theorem. Its corrected canonical-operation equation has a
complete Lean proof. The parent theorem retains a complete proof of its original
statement from the smaller coefficient identities.

New proved constructions and calculations:

- `finiteEvaluationSquare_nonempty`: normalized derived evaluation/direct-image square.
- `diagonalTrace_finiteEvaluation_projection`: its compatibility with derived limit projection.
- `diagonalTrace_finiteCanonical_supported`: the supported equation for the constructed operation.
- `diagonalTrace_supportedUnit_normalization`: the ordinary supported-source unit identity.

Remaining proof obligation (one new hole):

- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finitePush_unit`
  (`lem-sfb-diagonal-trace-finite-push-unit`): only the coefficient-unit component,
  with no degree-two arrow, supported class, arbitrary Hom operation, or Chern class.

The assigned module has zero sorries; the delivery adds exactly this one sorry.
The ordinary normalization lemma is proved, not split off. The result is a
statement repair and decomposition, not a claim to have proved the old false
assertion. No sorry is embedded in a definition, a private helper, or any
combining proof.

The normalized evaluation construction compiled in 13 seconds, the projection
calculation in 16 seconds, the ordinary supported-unit identity in 20 seconds,
and the geometric equation in 13 seconds. The full eight-file chain compiled
cleanly, including the supported calculation (13.3 seconds), the original parent
statement (9.4 seconds), and its unchanged direct importer
`Sheaf.Paper.DiagonalTraceFiniteDivisorAdjoint` (9.9 seconds). The unchanged
importer copy was removed after checking, so it is not part of this delivery.
Profiler options used during debugging have been removed. The former slow
projection conversion is factored into proved private generic lemmas; the final
file compiles within the normal 60-second limit.

## No longer needed

The parent's proof no longer imports
`Sheaf.Paper.DiagonalTraceFiniteAdjunctionSupported` or uses
`lem-sfb-diagonal-trace-finite-adjunction-supported`: an unspecified witness
satisfying only the supported equation is replaced by a real construction.
That existing module, currently held by C9, is left untouched. Its removal from
this route is recorded in the parent's proof dependencies.

The geometric module no longer publicly imports the supported half. It uses
the explicit evaluation interface instead. Its old direct proof dependencies
`lem-pur-coefficient-system-derived-comparison` and
`lem-sfb-diagonal-trace-exact-cone-projection` are replaced by the unit-component
lemma and the actual comparison. The exact-cone projection remains needed by
the smaller unit lemma; no global pruning of it is claimed. Existing presentation,
coefficient and supported-unit definitions remain needed in the parent route.

The evaluation interface itself does not import the finite Cartier-Chern
statement; only the supported calculation needs its completedSupportedUnit
interface. No blueprint unit statement or realized proof step is bypassed.

## Statement corrected

Only the intermediate arbitrary-function interface is corrected. Its old and
new signatures, the counterexample, and the complete citer audit are in the
change record and the node's statement_change. The only citer's statement stays
verbatim unchanged and its proof is adapted in this packet.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: agreement of an arbitrary function Phi on diagonal-supported
classes does not determine its values on every geometric class. For an
algebraically closed field of characteristic different from l, the two ruling
classes generate H²(P¹ × P¹, Z/l^(n+1)(1)); the diagonal-supported image spans
their sum. A ruling class lies outside that image, so Phi can be changed there
without affecting any supported equation. The source's operation is canonical
direct image, rather than an arbitrary set function. The old final proof step
asserting that the supported equation fixes that operation was unjustified.

The correction does not weaken a target or the parent theorem. It replaces the
bad intermediate assertion and adapts the consumer to the construction the
source actually uses. Edge cases of the new coefficient identities include
n=0 (the positive exponent is n+1) and the empty scheme; the identities are
functorial and unital in these cases as well.

## New nodes

`def-sfb-diagonal-trace-finite-evaluation` records the actual completed unit,
normalized evaluation square (with a proved existence theorem), and finite
comparison. These are constructions, not arbitrary witness choices.

`lem-sfb-diagonal-trace-finite-evaluation-projection` records the derived-functor
uniqueness argument reducing projection coherence to limit.post_π and the full
common-unit normalization.

`lem-sfb-diagonal-trace-supported-unit-normalization` records only the ordinary
coefficient-unit identity fixed by the source normalization.

`lem-sfb-diagonal-trace-finite-canonical-supported` records the fully written
supported calculation combining that ordinary seed and projection coherence.

`lem-sfb-diagonal-trace-finite-push-unit` isolates only the unit component of the
geometric comparison. Its source proof uses actual unital quotient maps,
coefficientPullback normalization, the exact-cone projection identity and the
normalized comparison units. Naturality in the geometric arrow is proved in
the assigned module rather than included in this remaining statement.

Change record: `coord/changes/C8-diagonal-finite-operation.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DiagonalTraceFiniteAdjunctionFactorization": "0a1e64555ad720fa62ea812d30d707ee24a985e9", "Sheaf.Paper.DiagonalTraceFiniteAdjunctionGeometric": "9da62e35b62ff318fd5c5063364ca0dea6e95f56", "Sheaf.Paper.DiagonalTraceFiniteCanonicalSupported": "0d5d4359ca48013dae9c7c36541f8e6509ef1b18", "Sheaf.Paper.DiagonalTraceFiniteEvaluation": "030cf4d6ed3ee5d4a69e243a3059a6127c696891", "Sheaf.Paper.DiagonalTraceFiniteProjection": "521209f4973b42984a9912acad12fe3e939c8ec2", "Sheaf.Paper.DiagonalTraceFinitePushUnit": "20f1a770f467d0fa4ebbbe6246a0513c97912735", "Sheaf.Paper.DiagonalTraceSupportedUnitNormalization": "644cafbeb49ff61caf61d5963fa2212b2e2d4bf6"}, "results": {"Sheaf.Paper.DiagonalTraceFiniteDivisorAdjoint": {"hash": "d010037f4deb8ff17b7644316767e8f77982b1bf", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T04:03:07+0800", "transitive": 0, "version": 1}
```

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
