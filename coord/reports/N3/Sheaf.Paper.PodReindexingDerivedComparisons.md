## What changed

The assigned theorem now assembles the requested `PodReindexingDerivedData` witness from
strictly smaller normalized obligations. The existing data definitions and their public
signatures were moved into `PodReindexingDerivedComparisonsCore`, which the assigned module
publicly imports and therefore reexports unchanged. The core split theorem supplies the
reduction/evaluation, limit/projection, unit, finite-model and full-limit-model laws. A second
split theorem supplies pullback normalization for the same assembled witness. The assigned
proof combines these six components into the original `PodReindexingDerivedData.Laws` predicate.

The change record is `coord/changes/N3-pod-reindexing-derived-comparisons-decomposition.md`. The two split obligations are named public theorems with their own DAG nodes. No existing
consumer needs adaptation; the direct importer `PodReindexingCompletionUnitTensor` compiles
against the reexported definitions and the repaired theorem.

## Proved and sorry left

The original theorem is proved:

- `WeilConjectures.podReindexingDerivedComparisons` (node
  `lem-pod-reindexing-derived-comparisons`).

Two strictly smaller proof obligations remain as named theorems:

- `WeilConjectures.podReindexingDerivedComparisonsCore` (node
  `lem-pod-reindexing-derived-comparisons-core`) leaves the five core comparison laws;
- `WeilConjectures.podReindexingDerivedComparisonsPullback` (node
  `lem-pod-reindexing-derived-comparisons-pullback`) is proved (reviewer FIX). The delivered
  form, normalization for every witness `R`, was false: the normalized realization is unique
  (`primitiveQuotientRealizations_unique`), so `R.pullback` twisted by `-𝟙` is a counterexample.
  The proved form gives a normalized replacement `p` for the `pullback` field by
  `primitiveQuotientPullbackModelExistence`. The item uses `{ R with pullback := p }`, and
  the five core laws do not read that field.

Holes closed: 1. Holes added: 1 (`podReindexingDerivedComparisonsCore`). Split off: 2, one of them proved. No definition contains `sorry`.

Validation: all three delivered modules compile, and the direct importer
`Sheaf.Paper.PodReindexingCompletionUnitTensor` compiles in the sandbox. The delivered theorem
therefore preserves the original flat `Laws` interface.

## No longer needed

`lem-pur-normalized-completed-operation-models` is no longer cited: the pullback normalization comes from
`lem-trf-primitive-quotient-pullback-model-existence` (reviewer FIX). The original strict-comparison import is rehomed into
the public core module, and the assigned module reexports that module. The original proof
dependencies remain used by the two split nodes: strict comparisons and the coefficient,
strict-limit, primitive-realization and normalized-completion model declarations are retained.

## Where the brief, the DAG or earlier work was wrong

The DAG treated the entire derived comparison package as one indivisible proof step, although
its conclusion is a conjunction of independent normalization interfaces. The existing source
already exposes the data structure and each predicate separately, so the proof can be reduced
faithfully by isolating the five comparison laws from the representative pullback normalization.
The original theorem statement and the order of all six `Laws` conjuncts are unchanged.

## New nodes

- `lem-pod-reindexing-derived-comparisons-core`: core derived comparison package omitting only
  pullback normalization.
- `lem-pod-reindexing-derived-comparisons-pullback`: prescribed pullback normalization for the
  assembled witness.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingDerivedComparisons": "8fa2575a52148c119f06a025cd723f76f1f94711", "Sheaf.Paper.PodReindexingDerivedComparisonsCore": "ed2a48935f8af21e0e105a8153879bd98e40b2ff", "Sheaf.Paper.PodReindexingDerivedComparisonsPullback": "e0cb19600c00f34775a4c6f428a8db1a2532f094"}, "results": {"Sheaf.Paper.AdicAmbientHomEvaluationComparison": {"hash": "bbfaf7d01205bc9f63062395db482061f6d3f51e", "status": "OK"}, "Sheaf.Paper.PodReindexingCompletionUnitTensor": {"hash": "6f89febbb6bfe7b7a78964b1f7236b01edd9f8cf", "status": "OK"}}, "seconds": 63, "time": "2026-10-28T07:14:24+0800", "transitive": 1, "version": 1}
```

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
