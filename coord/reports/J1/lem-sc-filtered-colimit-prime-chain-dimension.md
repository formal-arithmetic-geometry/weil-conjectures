# Stage-1 split: lem-sc-filtered-colimit-prime-chain-dimension

## Files written

- `dag/nodes/sec-curve-estimates/lem-sc-filtered-colimit-prime-chain-dimension.json`: item, split into two proof steps.
- `citations.json`: verbatim citation for the existing filtered-colimit elementwise node.

## Attachments

None. I searched `WeilConjectures/` in both source checkouts for the item id, Tag 06LK, and prime-chain/filtered-colimit terminology; no sorry-free project declaration states this item.

## WANTED

None. The Stacks source used here is available at `/home/ubuntu/c1-stacks-review/more-algebra.tex`; the repository's literature path is the recorded source path.

## Not duplicates

- `lem-sc-filtered-colimit-prime-chain-dimension` vs `lem-pc-filtered-colimit-commrings-elementwise`: the existing Mathlib-backed node states only element representation and eventual equality in a filtered colimit; this item proves strict contraction of finite prime chains and the resulting Krull-dimension bound.
- `lem-sc-filtered-colimit-prime-chain-dimension` vs `lem-sc-strict-henselization-dimension`: the existing node asserts equality of dimensions for a strict henselization; this item is the general filtered-colimit chain lemma used in its upper-bound step.
- `lem-sc-filtered-colimit-prime-chain-dimension` vs `lem-weil-pbc-strict-henselization-triples`: the existing node gives a strict-henselization filtered presentation; this item gives the independent finite-prime-chain argument for any filtered ring colimit.

## Review by J1

I read More on Algebra, Tag 06LK (the proof of `lemma-henselization-dimension`) in the Stacks source. Its converse inequality explicitly contracts a finite chain of primes in a directed colimit to one sufficiently large stage, then takes the supremum of the stage dimensions. The item statement matches that assertion and its dimension consequence.

Step 1 uses exactly the statement of `lem-pc-filtered-colimit-commrings-elementwise`: each selected separating element is represented at a stage. I checked that the node states this representative property, and that filteredness supplies a common later stage for the finitely many representatives. Contraction of a prime is prime, inclusions contract monotonically, and the selected element witnesses strictness; these are direct elementary properties of ring maps and prime ideals, so no additional node is needed. Step 2 is the definition of Krull dimension applied to the chain bound and is marked elementary.

I searched the DAG and blueprint for Tag 06LK, prime-chain contraction, and filtered-colimit dimension before deciding that no new node was needed. The existing elementwise node is a strictly weaker supporting fact rather than a duplicate. I tested the argument on a constant diagram, on a localization filtered diagram, and on the zero-dimensional field case; all give the stated contraction and bound. The Mathlib searches for the item were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and was not recorded as a match.

## What was wrong or incomplete

The imported item had no proof or proof dependencies despite being cited by the strict-henselization dimension argument. I supplied the missing finite-stage contraction and dimension steps and added the existing elementwise filtered-colimit node as a statement dependency.

## What remains

No new nodes were created. The item is ready for the second worker's reading.

## Second reading by J1

- Statement: checked against More on Algebra, Tag 06LK (`lemma-henselization-dimension`) and the definition node `def-weil-pbc-category-colimit`; verdict: correct after making the filtered diagram and colimit explicit.
- Step 1: checked against the finite-chain contraction paragraph of Tag 06LK and the statement of `lem-pc-filtered-colimit-commrings-elementwise`; verdict: the finite separating representatives and common filtered stage establish strictness, and contractions are prime.
- Step 2: checked against the concluding supremum argument of Tag 06LK and `def-weil-pbc-krull-dimension-ring`; verdict: elementary application of the dimension definition.
- New nodes: none; there are no new node statements to audit.
- Mathlib searches: checked the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch results; verdict: no existing prime-chain dimension declaration.

Changes made: expanded the item statement to introduce the small filtered category, commutative-ring diagram, and colimit explicitly, and added `def-weil-pbc-category-colimit` to `stmt_deps` so the statement is self-contained. No proof step or citation was otherwise changed.
