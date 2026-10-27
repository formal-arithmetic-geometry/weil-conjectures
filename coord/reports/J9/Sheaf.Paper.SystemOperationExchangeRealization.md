## What changed

Proved `WeilConjectures.FrobeniusExchange.compactIntegral_reduction` in
`Sheaf.Paper.SystemOperationExchangeRealization`. The proof specializes the existing
`integralExchange_reduction` to the proper/open system composite and transports it through
`compactRealization`. A proved private categorical helper cancels the mapped output
isomorphism and applies naturality of the pullback/reduction counit at the source.
All public statements, definitions and imports are unchanged. The proof uses explicit
component equations, keeps the chosen compact realization opaque, and locally exposes
only the simple realization and constructible-pullback aliases needed for categorical
simplification. The compact alpha/beta formula is reassociated as a natural transformation
before taking its component, avoiding the expensive pointwise normalization. Diagnostic
profiler options are removed from the delivery. The node's proof and the
declaration's docstring now record this categorical calculation rather than leaving
compact reduction among its obligations. The complete module compiled in 28.2 seconds
with the diagnostic profiler; those options are absent from the submitted source.

## Proved and sorry left

Closed one of the original thirteen holes:
`WeilConjectures.FrobeniusExchange.compactIntegral_reduction`.
Added zero holes and zero split-off statements.

The following twelve existing holes remain, all in namespace
`WeilConjectures.FrobeniusExchange` and owned by node
`def-weil-system-operation-exchange-realization`:

- `systemDirectEvaluationOrdinary_eq`
- `systemPullEvaluationOrdinaryInv_isIso`
- `systemDirectEvaluation_isIso`
- `systemExchange_evaluation`
- `systemOpenEvaluationInv_isIso`
- `systemOpenExchangeInv_isIso`
- `systemOpenScalarInv_isIso`
- `directImage_roos`
- `directImage_linear`
- `directAlpha_isIso`
- `compactRealization_existsUnique`
- `compactAlpha_isIso`

These retain their existing source citations and natural-language proofs. The partial
delivery closes the compact reduction obligation without decomposing it into new holes.

## No longer needed

No imports, nodes or modules are withdrawn. The compact reduction proof does not use
finite evaluation, `systemExchange_evaluation`, or geometric invertibility of the source
comparisons: its system map can be arbitrary. These declarations remain needed for the
module's other constructions and obligations. The five existing node proof dependencies
remain needed by the proofs already present. The blueprint unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The previous compact reduction docstring's reference to finite evaluation described a further
consequence, rather than a dependency of the displayed whole-system counit equation.
Counit naturality and transport through the specified realization suffice for this equation.
Searches through the required leanfinder, loogle and grep tools located the generic
naturality lemmas; no replacement theorem for this exact compact exchange was found.
No statement or definition repair was necessary.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
