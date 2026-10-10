# Stage 1 report: lem-pc-perfect-thick-closure

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-perfect-thick-closure.json`: split item.
- `dag/nodes/sec-picard-framework/lem-pc-perfect-two-out-of-three.json`: statement-only Stacks input, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-perfect-summand.json`: statement-only Stacks input, no Mathlib match.
- `citations.json`: verbatim citations for every proof-step dependency.

## Attachments

None. No sorry-free declaration in `WeilConjectures/` states the complete scheme-level thick-closure result.

## WANTED

None. The imported node and its source metadata identify Tags 08CR, 08CS, and Definition 08CM in `literature/stacks-project/cohomology.tex`; the proof is recorded against those tags.

## What was wrong or incomplete

The imported item was unsplit and had no proof. Its existing Mathlib search found only generic derived-category infrastructure. I added the two genuinely non-elementary closure inputs and did not create nodes for shifts or finite sums, since those follow directly from the strictly perfect presentation in `def-pc-perfect-complex`.

## Not duplicates

lem-pc-perfect-two-out-of-three vs lem-pc-perfect-thick-closure: the new node states only the distinguished-triangle two-out-of-three lemma for three named objects, while the item also asserts summand, shift, and finite-direct-sum closure.

lem-pc-perfect-summand vs lem-pc-perfect-thick-closure: the new node states only the direct-summand lemma for a decomposition K ≅ L ⊕ M, while the item is the conjunction of that clause with triangle, shift, and finite-direct-sum closure.

## Review by C1

I read the item, the `sec-picard-framework` chapter and `sk-thm-picard-duality` unit, and the existing definition node `def-pc-perfect-complex`. I also read the surrounding use sites in `lem-sc-pseudo-coherent-support-annihilation`: they need closure of the thick subcategory under triangles, shifts, sums, and summands, and they use the result for `D_{QCoh}(Y)` viewed inside `D(O_Y)`. The item statement retains all three clauses and its scheme/derived-category/perfect-complex hypotheses.

Step 1 cites `lem-pc-perfect-two-out-of-three`; that node states verbatim the same distinguished-triangle hypothesis and conclusion, with all three objects introduced. Step 2 cites `lem-pc-perfect-summand`; its statement explicitly gives perfectness of both summands from a perfect direct sum. Step 3 cites the definition node for the strictly perfect bounded finite-free presentation; shifting changes only the finite degree interval, and finite direct sums preserve boundedness and finite local freeness, so this is the elementary definition-level argument. The new nodes are statement-only as required and carry no hidden proof sketch.

For duplication checks I searched the whole DAG and blueprint for “perfect thick closure”, the Stacks tags 08CR/08CS, and the key terms “two out of three” and “summands perfect”; no existing node states either auxiliary result. For Mathlib I ran LeanFinder, Loogle, and Mathlib-source grep separately for each new node (and the item); the logs returned only generic derived-category or K-projective declarations, with no scheme-perfect closure theorem. The small edge cases are consistent: the zero complex and a one-term finite free complex remain perfect under shifts and finite sums, and a direct summand of a finite free term is covered by the strictly perfect definition.

## Second reading by C1

- Item statement: checked against Stacks Cohomology Definition 08CM and Lemmas 08CR/08CS; all three clauses and hypotheses are retained.
- Step 1: checked against Tag 08CR and the verbatim statement of `lem-pc-perfect-two-out-of-three`; verdict: exact use of the cited node.
- Step 2: checked against Tag 08CS and the verbatim statement of `lem-pc-perfect-summand`; verdict: the decomposition and both summand conclusions match.
- Step 3: checked against Definition 08CM and `def-pc-perfect-complex`; verdict: elementary after explicitly taking a common refinement and constructing shifts and termwise finite sums.
- `lem-pc-perfect-two-out-of-three`: checked against Tag 08CR, self-contained definitions, and zero-complex edge cases; verdict: sound statement-only auxiliary.
- `lem-pc-perfect-summand`: checked against Tag 08CS, self-contained definitions, and zero/direct-sum edge cases; verdict: sound statement-only auxiliary equivalent to the item's summand clause by renaming.

Changes made: rewrote Step 3 to spell out the common-refinement and termwise finite-sum argument, removing the vague presentation-transport phrase; no statement or citation changes were needed.
