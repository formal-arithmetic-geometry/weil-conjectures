## What changed

Proved `WeilConjectures.scalarHomOrdinary_isIso` in the assigned module. Present
exact ordinary scalar extension as a universal derived change-of-rings model.
Apply the existing normalized ringed tensor theorem. Its pure-tensor formula and
the good-complex square identify its chain and derived tensor comparisons with
`scalarOrdinaryTensorChain` and `scalarClosedTensor`, using their existing
uniqueness theorems. The completed coefficient basis, finite biproduct comparison
and ULift reindexing supply the free-module hypothesis. The ringed Hom theorem
then identifies its natural isomorphism with the specified evaluation transpose.
The proof applies to arbitrary unbounded inputs.

Added proof imports of `Sheaf.Paper.CompletedIntegralFiniteFree`,
`Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeTensor`, and
`Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeHom`. Keep the recorded tensor
models locally irreducible while applying their API. Updated the item's DAG proof
and proof dependencies. In the private small-site completeness helper, name the
existing family of slice derived-category instances and use its value explicitly,
so instance inference need not rediscover it through a large conversion.
No public signature, definition body or public import changed. No other existing
Lean module changed. The full item compiled successfully in 55.2 seconds with
profiling enabled; profiling options and all diagnostic modules were removed
before delivery. The clean delivery probe also compiled in 55.8 seconds; its sole style warning
was corrected before resubmission. The delivery tool performs the final preflight.

## Proved and sorry left

One of nine original holes closed:
`WeilConjectures.scalarHomOrdinary_isIso`.
No holes added or split off; eight original holes remain unchanged, all attached
to `lem-pur-integral-operations-scalar-extension`:

- `WeilConjectures.scalarPullbackLevel_existsUnique`.
- `WeilConjectures.scalarPullbackTower_existsUnique`.
- `WeilConjectures.scalarTensorLevel_existsUnique`.
- `WeilConjectures.scalarTensorTower_existsUnique`.
- `WeilConjectures.scalarPullbackOrdinary_existsUnique`.
- `WeilConjectures.scalarTensorOrdinary_existsUnique`.
- `WeilConjectures.scalarCompletion_existsUnique`.
- `WeilConjectures.scalarOperationsOrdinary_tower`.

## No longer needed

This item's Hom proof no longer needs the existential wrapper
`lem-sf-ringed-finite-free-hom-base-change`, module
`Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange`: its normalized tensor and Hom
clauses are applied directly to the already fixed models. Removed that wrapper
from this node's proof dependencies. Other users may still need the wrapper; no
module or node is withdrawn. The unchanged remaining comparison clauses retain
their planned dependencies. No original explicit import is removed.

## Where the brief, the DAG or earlier work was wrong

No statement repair was required. The blueprint unit's coefficient-compatibility
route is preserved. An attempted completion proof compared exact derived models
and composed with the existing completed scalar comparison. Its normalization
calculation still exceeded the compile-time limit; it is not included in this
partial delivery. The original completion hole and its proof plan are preserved.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
