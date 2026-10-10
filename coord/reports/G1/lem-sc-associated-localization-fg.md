Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-associated-localization-fg.json`: item split into three elementary proof steps; no new nodes.
- `citations.json`: six verbatim statement quotes covering both localization definition dependencies in each step.

Attachments: none.

WANTED: none.

The item had no declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`. The existing DAG node was the converse part of Stacks Algebra Lemma 0310 (tag 0310), while its parent cites it as the final step of Lemma 058A. I retained the item statement and added the finite-generator denominator-clearing proof. The Mathlib searches found only radical-based `IsAssociatedPrime` localization results, so the item is not a Mathlib leaf.

## Review by G1

I read the item source, Stacks `algebra.tex`, Lemma 0310 (tag 0310), lines 15393–15418, and checked the statement against the source: the ring is arbitrary, the prime is finitely generated, and the localized annihilator is the maximal ideal `p R_p`. I also read both cited definition nodes. Step 1 uses their fraction and zero criteria to show `Ann_R(m)` is contained in `p`; primality supplies the contraction argument. Step 2 uses the same fraction criterion for each finite generator, multiplies the denominators, and checks nonzeroness by the fact that a denominator outside `p` cannot annihilate an element whose localized annihilator is `p R_p`. Step 3 uses the generator equations and primality to prove the new element's annihilator is exactly `p`; all three steps are direct calculations from the cited definitions and are marked elementary. I tested the calculation on a principal prime and on the zero module edge case (the hypothesis excludes the latter because `p R_p` is proper). The search log records LeanFinder, Loogle, and Mathlib grep results; all candidates use Mathlib's radical notion and therefore do not state this annihilator result.

## Second reading by G1

- Item statement: checked against Stacks Algebra Lemma 10.66.3, tag 0310, clause (2), lines 15393–15418; the arbitrary commutative ring, finitely generated prime, localization, and annihilator conclusion agree hypothesis by hypothesis.
- Step 1: checked the cited localization-at-prime and module-localization statements; fraction equality gives membership in `p R_p`, and primality gives `Ann_R(m) ⊆ p`; elementary and correctly scoped.
- Step 2: checked the module localization zero criterion for each generator, multiplication of the finitely many denominators (including the empty-product case), and the unit/nonzero argument in the localized ring; elementary and valid under the stated annihilator hypothesis.
- Step 3: checked the generator containment and the converse using Step 1 and primality; this proves exact equality of annihilators and is elementary.
- New nodes: none; the split adds no node requiring B1–B7 or duplicate/search review.
- Edge cases: tested a principal prime, the zero prime with zero generators, and the zero module; the latter cannot satisfy the proper maximal-ideal annihilator hypothesis.

Changes made: added this second-reading audit only. No mathematical or citation changes were needed.
