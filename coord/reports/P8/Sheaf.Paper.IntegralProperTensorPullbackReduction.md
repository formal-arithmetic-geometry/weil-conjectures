## What changed

Proved `WeilConjectures.IntegralProjectionReduction.integralProperTensorPullbackReduction`
by direct naturality of the actual reconstruction counit, transport along the
datum's pullback and tensor equalities, and cancellation of the comparison
isomorphisms. Private helpers implement the generic counit calculation and its
canonical completed specialization, following the proved private calculations
in `DerivedPullbackTensorIso`. The public statement and public imports are
unchanged. Updated the item's node to match the Lean proof.
The required remote single-file compile passed cleanly in 18.0 seconds.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.IntegralProjectionReduction.integralProperTensorPullbackReduction`
(node `lem-sf-integral-proper-tensor-pullback-reduction`). No holes added; none left
in the delivery. All private theorems are proved. No definitions contain holes.

## No longer needed

The item no longer directly needs `lem-coef-integral-residue-tor`
(`Sheaf.Paper.IntegralResidueTor`): the requisite actual counit invertibility is
already supplied by `pullbackTensorComparisonCounits`. This does not withdraw
that module, which remains needed elsewhere and by the coordinate definitions.
No imports or modules are removed. No new decomposition is introduced. The
bundled, unfinished public theorem `derivedPullbackTensorIso` is not applied;
its private canonical reduction calculation is reproduced locally with a
complete proof instead.

## Where the brief, the DAG or earlier work was wrong

The proposed canonical counit calculation already has a proved private version
in `DerivedPullbackTensorIso`, although its bundled public theorem is unfinished.
The proof follows that calculation in private helpers, then supplies the datum
equality transport and the conversion to inverse components. No new statements
or cross-unit theorem dependencies are needed. The unit's route is preserved.
No nonzero-input, nonempty-scheme, or nonidentity-map hypothesis is used.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
