## What changed

Filled `WeilConjectures.integralScalarCounitNormalization` in the assigned module.
The statement is unchanged. The new proved modules
`Sheaf.Paper.IntegralScalarOrdinaryModelComparison` and
`Sheaf.Paper.IntegralScalarOrdinaryModelCoherence` compare
the two ordinary scalar models, including their specified completion maps,
multiplication and associators. Its public statement mentions only public models;
all tensor-presentation helpers remain private.
All three modules passed single-file compilation in import order. Profiling options
were removed before the required delivery preflight.
The proof then applies `scalarModelUnit` and `scalarModelAssociativity`, cancels the
completion isomorphisms at the intrinsic complete inputs, and transposes the resulting
equations using the actual reduction/limit counit. The node records these steps.

## Proved and sorry left

Closed the one original hole, `WeilConjectures.integralScalarCounitNormalization`
(node `lem-trf-integral-scalar-counit-normalization`). Both conjuncts are proved.
No new holes are added; no textual `sorry` remains in any of the three delivered modules.
The new theorem `WeilConjectures.integralScalarOrdinaryModelCoherence`
(node `lem-trf-integral-scalar-ordinary-model-coherence`) and
`WeilConjectures.integralScalarOrdinaryModelComparison`
(node `lem-trf-integral-scalar-ordinary-model-comparison`) are fully proved.
The proof uses the existing named obligations `WeilConjectures.scalarModelUnit` and
`WeilConjectures.scalarModelAssociativity` as the stage-3 dependency plan prescribes.
This is a proof from existing declarations, not a new split of this obligation.

## No longer needed

None of the five original declared mathematical dependencies is pruned.
The new coherence node records the lower dependencies used by its proof;
the assigned module imports its proved public theorem. The two existing
public imports are retained unchanged for the statement. No other module is withdrawn.
No scheme pullback comparison or isomorphism-pullback coherence is needed for the
scalar calculation.

## Where the brief, the DAG or earlier work was wrong

The comparison in `IsomorphismComparisonScalarExtension` cannot be imported here:
that module reaches the assigned module through pullback realization. The proof uses
the already available lower construction `ordinaryScalarModelIso` instead and proves
its derived unit and associator compatibility privately. No existing declaration,
shared definition or target statement is changed.

## New nodes

`lem-trf-integral-scalar-ordinary-model-coherence`, realized by
`WeilConjectures.integralScalarOrdinaryModelCoherence` in the new module
`Sheaf.Paper.IntegralScalarOrdinaryModelCoherence`, proves the canonical ordinary
model comparisons, including completion, unit and associator compatibility.
It is a proved part of the argument, with no new hole. Its construction is supplied
by the new proved comparison module. A complete single-file
version of the assigned proof was accepted logically but exceeded 60 seconds.
The tensor-model construction, its coherence calculation and the counit transpose
are separate files so that each can be checked independently within the limit.
No existing shared definition or interface is changed, and no change record is needed.

`lem-trf-integral-scalar-ordinary-model-comparison`, realized by
`WeilConjectures.integralScalarOrdinaryModelComparison` in
`Sheaf.Paper.IntegralScalarOrdinaryModelComparison`, proves the pure-tensor
isomorphism and its counit-normalized derived lift, including completion
compatibility. It exposes the tensor isomorphism existentially, so its public
statement refers only to public constructions. It adds no hole.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
