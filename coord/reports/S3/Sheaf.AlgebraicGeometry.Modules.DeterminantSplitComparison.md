## What changed
Added a proof reduction in `DeterminantSplitComparison.lean`, importing a new local construction module. The target theorem combines a sectionwise local comparison theorem with a restriction compatibility theorem.

## Proved and sorry left
The target theorem `determinant_split_comparison_exists` is proved by applying the two named intermediate theorems. Sorries remain in `determinant_split_comparison_local` and `determinant_split_comparison_restriction`, with nodes `new-determinant-split-local` and `new-determinant-split-restriction`.

## No longer needed
No imports or existing nodes were pruned.

## Where the brief, the DAG or earlier work was wrong
The original proof plan requires substantial sheafification and local basis arguments; these are split into two strictly smaller intermediate statements.

## New nodes
`new-determinant-split-local` and `new-determinant-split-restriction` are new proof obligations in the local construction module.

## Earlier second reading (a previous round; superseded)
Pending the independent second reading.

## Second reading by S3

1. **Comparison with the repository.** I diffed the delivered target module against the repository version. The theorem statement and all existing declaration signatures are unchanged; the only target changes are the proof and a proof-only import. The added local module and two DAG nodes are declared explicitly.

2. **Compilation and proof status.** Both delivered Lean files compile with `lcompile.py --all`. The target theorem `determinant_split_comparison_exists` is closed. The only remaining `sorry`s are the named split obligations `determinant_split_comparison_local` and `determinant_split_comparison_restriction`; there are no sorries in definitions or forbidden axioms in the delivered code.

3. **Statement review.** The two split-off statements are strictly smaller than the target: one constructs the local family and generator formula, and the other proves restriction compatibility from that formula. Their hypotheses and conclusions match the Lean declarations and the target's use of them; they do not restate the target.

4. **Proof route and pruning.** The target proof follows the shortest available reduction to the two local obligations and passes the supplied lifts to the restriction lemma. The proof-dependency record was updated to these two nodes. No existing import or node became unused, and no unit-level route was bypassed.

5. **DAG and unit consistency.** The new nodes contain matching declarations, source, proof origin, and split status. The target node now records the two actual proof dependencies and reduction steps. The `sk-thm-picard-rr` unit record remains unchanged because this local determinant construction does not realize a unit statement or step.

I changed the report by adding this second-reading record and synchronized the target node's proof metadata with the Lean proof. No mathematical statement or definition was changed.
