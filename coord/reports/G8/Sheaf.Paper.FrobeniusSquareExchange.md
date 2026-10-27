## What changed

Proved `WeilConjectures.FrobeniusExchange.intrinsicCompactificationComparison_refinement`
in `Sheaf.Paper.FrobeniusSquareExchange`. Private proved categorical calculations
handle naturality under conjugation and cancellation of an equivalence unit/counit.
The proof uses the existing coherence theorem and the recorded fixed-witness
refinement construction. The node proof is updated to describe the argument.
No public signature, existing definition, import, or source-library file is changed.
The private `coordinateOrigin` explicitly packages an object and its retained witness;
its private normalization theorem is proved in the same module.
The unused-section-variable linter is disabled locally to avoid its expensive
scan of the large existing section; kernel and theorem checking are unchanged.

## Proved and sorry left

Closed one of the original six holes:
`WeilConjectures.FrobeniusExchange.intrinsicCompactificationComparison_refinement`.
No holes added and no statements split off.

Five original holes remain, all attached to
`def-weil-operation-exchange-coefficient-descent`, with their existing source and
proof docstrings:

- `WeilConjectures.FrobeniusExchange.intrinsicCompactificationCoherence`
- `WeilConjectures.FrobeniusExchange.pullback_linear`
- `WeilConjectures.FrobeniusExchange.modelScalarMap_isIso`
- `WeilConjectures.FrobeniusExchange.stageBeta_coherence`
- `WeilConjectures.FrobeniusExchange.stageExchange_compatible`

The closed theorem still depends on the existing coherence obligation; this
is a proof from the planned declarations, not an axiom-free completion of the
whole module.

## No longer needed

None. No imports, modules, nodes, or unit steps are pruned. No additional
mathematical dependency is introduced. The refinement normalization is a
coordinate calculation from the existing construction, so no separate new
statement node is needed.

## Where the brief, the DAG or earlier work was wrong

The previous DAG proof text listed refinement normalization among the remaining
obligations; it now records the completed calculation. The original unmodified
module exceeded the single-file compile budget in the initial check. Profiling
identified a large unused-section-variable lint cost; the proof context disables
that lint without changing any public declaration or mathematical meaning.

Change record: `coord/changes/G8-frobenius-refinement-proof-context.md`.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
