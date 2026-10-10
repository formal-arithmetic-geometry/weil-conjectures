1. Files written:
- `dag/nodes/sec-curve-estimates/lem-sc-faithfully-flat-local-dimension.json`: split statement, no Mathlib exact match.
- `dag/nodes/sec-curve-estimates/lem-sc-flat-going-down.json`: Mathlib leaf `Algebra.HasGoingDown.of_flat`.
- `dag/nodes/sec-curve-estimates/lem-sc-going-down-surjective-dimension.json`: unsplit Stacks statement, no direct Mathlib match.

2. Attachments:
- `lem-weil-pbc-faithfully-flat-surjective-spectrum` is the existing faithful-flat spectrum-surjectivity node used in step 2.

3. WANTED:

4. What was checked and corrected:
The item was read against Algebra Tag 00OH and the lower-bound sentence in the proof of More Algebra Tag 06LK. The original item had no proof and omitted the faithful-flat definition from `stmt_deps`; that dependency is now present. I searched the whole DAG and blueprint for Tags 00OH and 00HS and for going-down/dimension wording. The existing node `lem-weil-pbc-faithfully-flat-surjective-spectrum` states exactly the spectrum-surjectivity clause, so I reused it rather than duplicating it. The new flat-going-down node is the exact Tag 00HS fact and its Mathlib declaration was checked by LeanFinder and Loogle; the source grep command returned no match and is recorded as such. The new general node states Tag 00OH with all rings, the going-down hypothesis, the contraction map, and the Krull-dimension conclusion introduced explicitly. Its three searches found only order-theoretic or Noetherian generalizations, so it remains statement-only.

Step 1 uses the flat-going-down statement exactly and applies because faithful flatness includes flatness. Step 2 uses the existing node's exact faithful-flat hypothesis and contraction-map conclusion. Step 3 applies the general node to `A -> B`; the local-ring and local-map assumptions are stronger than needed and introduce no hidden hypothesis. I checked edge cases such as an identity local map and a field extension (both give equality), and the zero-dimensional local case. Every citation quote in `citations.json` is copied verbatim from its node statement. No source statement was changed.

5. What could not be finished:
No direct arbitrary-ring Mathlib theorem packages Tag 00OH, so that general implication remains an unsplit statement node for later proof work.

## Not duplicates
lem-sc-flat-going-down vs lem-sc-faithfully-flat-local-dimension: the new node states the flatness-to-going-down implication, while the item states a dimension inequality for faithfully flat local maps.
lem-sc-flat-going-down vs lem-pc-dim-base-change: the new node is the arbitrary-ring prime-chain lifting theorem 00HS, while the existing node concerns dimension under field extension and does not state going down.
lem-sc-flat-going-down vs lem-weil-pbc-flat-height-formula: the new node applies to arbitrary rings and states going down, while the existing node is a Noetherian height formula with a fibre-dimension summand.
lem-sc-going-down-surjective-dimension vs lem-sc-faithfully-flat-local-dimension: the new node is the general 00OH implication with explicit going-down and spectrum-surjectivity hypotheses; the item is its faithfully-flat local specialization.

## Review by F1
I read the Stacks algebra source locations for Tags 00OH, 00HS, and 00HQ and compared each hypothesis with the item and the three proof steps. Step 1 cites the flat-going-down node, which explicitly states the prime-chain lifting property; step 2 cites the existing faithful-flat spectrum node, which explicitly states surjectivity of contraction on primes; step 3 cites the general 00OH node, which explicitly states the same dimension inequality under those two hypotheses. The new Mathlib leaf records `Algebra.HasGoingDown.of_flat` at `GoingDown.lean:155`; its statement is exactly the going-down property for a flat algebra. I also verified the existing spectrum leaf's statement before quoting it. The new general node has no proof steps by design and carries the three recorded Mathlib searches. I checked small cases (identity maps, fields, and zero-dimensional local rings) and found no mismatch or missing hypothesis. The only correction to the imported item was adding the faithful-flat definition dependency and replacing the empty proof with these three sourced steps.

## Second reading by F1
Step 1 checked against Algebra Tag 00HS (lemma-flat-going-down) and `lem-sc-flat-going-down`; the flatness implication and prime-chain lifting hypotheses agree.
Step 2 checked against Algebra Tag 00HQ (lemma-ff-rings), implication (1) => (2), and `lem-weil-pbc-faithfully-flat-surjective-spectrum`; contraction-surjectivity agrees exactly.
Step 3 checked against Algebra Tag 00OH (lemma-dimension-going-up) and `lem-sc-going-down-surjective-dimension`; going down plus surjective spectrum gives the stated dimension inequality.
Node `lem-sc-flat-going-down` checked against Tag 00HS and `Algebra.HasGoingDown.of_flat` at `Mathlib/RingTheory/Ideal/GoingDown.lean:155`; its Loogle zero-hit verdict and recorded searches are accurate.
Node `lem-sc-going-down-surjective-dimension` checked against Tag 00OH; all rings, the contraction map, going-down, surjectivity, and Krull dimension are self-contained, with no exact Mathlib declaration found.
The existing `lem-weil-pbc-faithfully-flat-surjective-spectrum` attachment was reread and supplies exactly Step 2, so no duplicate node is needed.
Small cases checked: identity local maps, field extensions, zero-dimensional local rings, and the zero ring convention.
Changed `lem-sc-flat-going-down` only by correcting its Loogle verdict from `match` to `no match`, since the recorded query returned zero hits. No mathematical statement or proof step required alteration; the item already has both definition dependencies. Dry-run preflight passed after the repair.
