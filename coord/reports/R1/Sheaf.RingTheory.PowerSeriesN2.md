## What changed

Added `Sheaf.RingTheory.PowerSeriesN2Aux`, isolating the N-2 conclusion as
`PowerSeries.isN2_power_series`. The target theorem now combines this theorem
with Mathlib's Noetherian and domain instances. Added the proof-only import
`Mathlib.RingTheory.PowerSeries.Ideal` for the Noetherian instance and removed
the unused proof imports from the target module.

## Proved and sorry left

`PowerSeries.noetherian_domain_isN2` is proved. The new theorem
`PowerSeries.isN2_power_series` remains sorry and is recorded by node
`lem-weil-pbc-power-series-n2-aux`.

## No longer needed

The target proof no longer needs `IsN2OfFiniteExtension`,
`N2AscendsFiniteDomainExtension`, `PowerSeriesNormalDomain`,
`PowerSeriesQuotientVariables`, or `TateN2CompletePrincipal`; these imports and
their corresponding lower proof dependencies are pruned from this module.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan is substantially longer than needed for the
Noetherian and domain conjuncts: both are existing Mathlib instances. The
remaining N-2 argument is isolated as a strictly smaller theorem.

## New nodes

`lem-weil-pbc-power-series-n2-aux` records the isolated N-2 assertion and its
source proof plan.

## Earlier second reading (a previous round; superseded)

Pending the independent second reading; the target proof compiles and preserves
its original signature, while the isolated auxiliary theorem is strictly the
N-2 conjunct and has a matching node.

## Second reading by R1

1. Compared `PowerSeriesN2.lean` with the repository version. The theorem signature is unchanged byte for byte; only proof-only imports and the proof body changed. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. The target proof compiles, and the only remaining `sorry` is the named auxiliary theorem `PowerSeries.isN2_power_series`, with node `lem-weil-pbc-power-series-n2-aux`; no hollow definition or forbidden declaration was found. Verdict: pass, with the auxiliary hole intentionally open.
3. Checked the split statement against the source argument and edge shape: it is exactly the N-2 conjunct, while the target combines it with the standard Noetherian and domain instances. It is strictly smaller than the target and retains the original hypotheses and conclusion. Verdict: pass.
4. Checked the proof route and pruning. The target uses Mathlib instances for the first two conjuncts and the auxiliary theorem for N-2; removed imports are proof-only and listed above. The unit route is represented by the auxiliary node and its source proof plan. Verdict: pass.
5. Checked the DAG nodes against the Lean declarations and proof dependencies. The target node records the auxiliary dependency, and the auxiliary node records its theorem, module, declaration, source, and split status. Verdict: pass.

Changed only this second-reading report section; no Lean proof or statement required repair.
