## What changed

The item theorem now combines two strictly smaller intermediate theorems.  `chain_shift_presentations` supplies the two `ChainShift` structures, and `chain_shift_reindexing_square` supplies the comparison square for supplied structures.  The item imports both proof modules and packages their results.

## Proved and sorry left

The item declaration `chain_shift_part_exists` is proved by applying the two split statements.  Two split-off declarations remain sorry: `chain_shift_presentations` (node `new-pod-reindexing-chain-shift-presentations`) and `chain_shift_reindexing_square` (node `new-pod-reindexing-chain-shift-square`).

## No longer needed

No imports or declared dependencies were pruned; the item still uses the coherence-data definitions through the two intermediate statements.

## Where the brief, the DAG or earlier work was wrong

The original proof plan combines two independent obligations: constructing the signed product Hom shifts and proving their comparison square.  They are now represented as separate strictly smaller nodes so each can be proved independently.

## New nodes

`new-pod-reindexing-chain-shift-presentations` is stated in `lean/Sheaf/Paper/PodReindexingChainShiftPresentations.lean`.

`new-pod-reindexing-chain-shift-square` is stated in `lean/Sheaf/Paper/PodReindexingChainShiftSquare.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingChainShiftPresentations": "a70657cd8b747eb6cd28637b7175d153c91b858e", "Sheaf.Paper.PodReindexingChainShiftSquare": "ce6e8eb94e749270857fbcde8a907860bd64d905", "Sheaf.Paper.PodReindexingShiftChainPart": "89ed092b6120fad2565dc85a083f52c6d980b3d8"}, "results": {}, "time": "2026-10-28T08:17:50+0800", "transitive": 0, "version": 1}
```

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
