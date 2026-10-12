## What changed
Split the clopen assembly proof into two strictly smaller transfer lemmas (the first four and last four assertions), and assembled them in the target theorem.

## Proved and sorry left
The target theorem `assertions_constant_of_isClopen` is proved by a constructor from the two transfer lemmas. The new declarations `clopen_first_four` and `clopen_last_four` remain sorry and are recorded as new nodes.

## No longer needed
The target proof does not directly use the six original proof dependency nodes; they are deferred to the two transfer lemmas: `lem-weil-pbc-etale-sheaf-clopen-product`, `lem-weil-pbc-finite-coproduct-cohomology-assembly`, `lem-weil-pbc-finite-pushforward-cohomology`, `prop-constructible-pullback`, and `lem-weil-pbc-cohomology-pullback-functorial`.

## Where the brief, the DAG or earlier work was wrong
The original module had no implementable Lean proof of the large componentwise argument; it required explicit intermediate transfer statements.

## New nodes
`lem-pbc-k2-clopen-constant-assertions-first` and `lem-pbc-k2-clopen-constant-assertions-last` record the two intermediate transfer statements.

## Second reading by Y3

1. Compared the delivered target module with the repository version. The target theorem signature is byte-for-byte unchanged; the two added declarations are strictly smaller conjunctions. Verdict: pass.
2. Compiled all three delivered Lean modules with `lcompile.py --all`. They compile; the only remaining holes are the two named split lemmas, each with a matching node. No definitions, axioms, unsafe declarations, or forbidden constructs were added. Verdict: pass.
3. Checked the split statements against `Assertions`: the first lemma is exactly C1--C4 and the second exactly C5--C8, so each is true and strictly simpler than the target. Their docstrings state the source and reduction. Verdict: pass.
4. Checked the proof route and imports. The target uses both transfer lemmas; each node records the original clopen assembly dependencies. No import was removed, and the unit route remains the finite clopen assembly step. Verdict: pass.
5. Updated the target and split node proof records to match the Lean route and corrected the split node statements to their actual signatures. Verdict: pass.

Changed the two split node records and the target node proof metadata; no Lean proof text was changed.
