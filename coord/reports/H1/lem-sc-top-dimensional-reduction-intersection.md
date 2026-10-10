1. Files written: item node (split) and `citations.json`.
2. Attachments: none.
3. WANTED: none.
4. What was wrong: an attempted child restated Tag 0BES and was removed as D1. The item now carries the source's direct leading-coefficient argument and positivity consequence as steps.
5. What could not be finished: no Lean proof is written at stage 1.

## Review by H1

I read the Tag 0BES source in `varieties.tex` and the neighboring intersection-number nodes. Step 1 spells out the source's “immediate from numerical-polynomial-leading-term and definitions” argument; Step 2 is the elementary positivity of a finite weighted sum. I checked `d=0` and integral `X`. Mathlib searches for the item were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such. No child node remains, avoiding a duplicate Tag 0BES node.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Second reading by H1

- Item statement: checked against Varieties Lemma 33.44.4, Tag 0BES (label `lemma-intersection-number-in-terms-of-components`), including the proper scheme, nonempty closed subscheme, arbitrary invertible modules, top-dimensional components, generic-point lengths, and the displayed weighted sum; verdict: repaired to agree hypothesis by hypothesis.
- Proof step 1: checked against the Tag 0BES proof at the source line; verdict: elementary leading-coefficient argument retained and made precise using the explicitly defined multiplicities.
- Proof step 2: checked against the positivity use in Tag 0BEV; verdict: elementary positivity of a finite sum with positive weights retained.
- Definitions: checked every notion against its cited definition node (`def-sc-intersection-number`, `def-weil-closed-immersion`, `def-weil-irreducible-components`, `def-sc-generic-point`, and `def-weil-pbc-module-length`); verdict: all are now cited in the self-contained statement.
- Mathlib searches: checked `searches.jsonl`; verdict: the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch searches are present and no new node requires additional searches.
- Small cases: checked `d=0` (the sum is over zero-dimensional components), an integral scheme (one component with multiplicity one), and the empty scheme (excluded by the nonempty hypothesis); verdict: statement behaves as intended.

Changes made: replaced the specialized and informal self-intersection statement with the exact Tag 0BES component formula, added all missing definition dependencies, corrected the source label, and clarified both proof steps. No child node was added because Tag 0BES is the item itself and the remaining argument is elementary.
