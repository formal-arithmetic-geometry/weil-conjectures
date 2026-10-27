## What changed

The item now imports two proof modules and combines their proved conjuncts by `constructor`.
The identity and composition conjuncts are named public theorems in
`Sheaf.Paper.AdicReindexingIdentity` and `Sheaf.Paper.AdicReindexingComposition`.
Their proofs remain split obligations with documented source arguments.

## Proved and sorry left

The parent declaration `normalized_reindexing_functoriality` is reduced to the two strictly
smaller conjunct statements and compiles. Two sorries remain: `normalized_reindexing_identity`
and `normalized_reindexing_composition`, each with a corresponding DAG node below.
No sorry occurs in a definition.

## No longer needed

No proof dependency imports were removed. The original four planned proof dependencies are
retained as source material for the two split obligations.

## Where the brief, the DAG or earlier work was wrong

The original module imported `Sheaf.Paper.AdicRealizationFamilyData`, which is the current
canonical module; the earlier global-build record referred to an absent older import name.
The parent proof plan is a substantial categorical normalization argument, so it is reduced
into its identity and composition equations rather than asserting the parent under another name.

## New nodes

`lem-sf-adic-reindexing-functoriality-id` records the identity conjunct.
`lem-sf-adic-reindexing-functoriality-comp` records the composition conjunct.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AdicReindexingComposition": "3640d2da6bf51b8d7421ad5394267d891602625f", "Sheaf.Paper.AdicReindexingFunctoriality": "bf857425a90d47854bbe0ca74d81cdad54f17e62", "Sheaf.Paper.AdicReindexingIdentity": "00653206d957139656b4e4dccf988b616740ff19"}, "results": {}, "time": "2026-10-28T02:27:50+0800", "transitive": 0, "version": 1}
```

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
