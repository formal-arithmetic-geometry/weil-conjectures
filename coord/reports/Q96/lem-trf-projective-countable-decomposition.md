# Stage-1 report: lem-trf-projective-countable-decomposition

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-projective-countable-decomposition.json`: split statement; no Mathlib match for the Kaplansky decomposition.
- `dag/nodes/sec-trace-formula/lem-trf-projective-kaplansky-direct-summand.json`: new unsplit statement node for Stacks Tag 058X; no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited node at every proof step.
- `searches.jsonl`: the eight searches run through `msearch.py` (four for the item and four for the new node).

## Attachments

None. The source checkout has no declaration tagged `(blueprint: lem-trf-projective-countable-decomposition)` and no sorry-free declaration stating this item.

## New nodes

`lem-trf-projective-kaplansky-direct-summand` records Tag 058X, the direct-summand theorem used by Tag 058Y. It is strictly smaller than the item: it produces countably generated modules but does not assert they are projective. Its statement introduces the ring, the module decomposition, countable generation, the retract maps, and the resulting decomposition. The whole DAG and blueprint were searched for Tag 058X, “Kaplansky”, and the direct-summand/countably-generated formulation; no duplicate node or blueprint statement was found.

## Not duplicates

- `lem-trf-projective-kaplansky-direct-summand` vs `lem-weil-pbc-projective-direct-summand`: the new node decomposes a retract of a countable direct sum; the existing Mathlib leaf only transfers projectivity to a retract.
- `lem-trf-projective-kaplansky-direct-summand` vs `lem-weil-pbc-projective-direct-sum-family`: the new node gives a countably generated decomposition for an arbitrary retract; the existing leaf says a prescribed direct sum of projectives is projective.

## Sources and searches

I read `literature/stacks-project/algebra.tex` at Tags 058X and 058Y, including the full transfinite construction in the proof of 058X and the one-paragraph reduction in 058Y. I also read the statements of `def-weil-pbc-projective-module`, `def-weil-pbc-free-module`, and the existing Mathlib leaf `lem-weil-pbc-projective-direct-summand`. The item and new node were searched with LeanFinder, LeanSearch, Loogle, and Mathlib grep using the exact queries recorded in `searches.jsonl`; the returned declarations were generic direct-sum/projectivity infrastructure and none states Kaplansky's decomposition.

## Review by Q96

Step 1 uses the projective definition's split map into a free module and the free-module basis equivalence; I verified that these statements provide exactly the maps and direct-sum presentation used, including the empty-basis case. Step 2 applies the new Tag 058X node with $M=F$ and the retract maps from step 1; its statement supplies precisely the countably generated modules and the isomorphism, with no finiteness assumption. Step 3 uses only the canonical inclusion/projection maps of a direct sum and transports them across the displayed isomorphism; the cited existing node explicitly states that such a retract of a projective module is projective. I checked the arbitrary-ring and arbitrary-index hypotheses against both Stacks tags and retained the zero-module edge case. I corrected the imported empty proof by making the 058X invocation and the summand-projectivity argument explicit, and I declared the off-unit retract lemma as a generic tool use because it is the standard projectivity-closure fact required by the source route.

## What was wrong or incomplete

The imported node had no proof steps or proof dependencies, although Tag 058Y relies on Tag 058X and on the retract closure of projectivity. The new split supplies those dependencies and preserves the original statement exactly.

## What remains

The new 058X node is intentionally statement-only and remains in the stage-1 queue for a later worker.
