# Delivery report

1. Files written:
   - `lem-sc-p1-graded-degree-component-exact.json`: statement node, split; no new nodes and no Mathlib leaves.
   - `citations.json`: no node citations, because all three proof steps are elementary consequences of the stated exact sequence, degree preservation, and direct-sum decompositions.
2. Attachments: none.
3. WANTED: none.
4. The item was unsplit. I kept its self-contained statement and supplied the direct proof corresponding to Algebra, Section 00JL. No existing DAG or blueprint node states this exact componentwise exactness result, and no exact Lean declaration was found by searching the source checkout.
5. Nothing remains unfinished.

## Review by K1

I read the item source recorded as `literature/stacks-project/algebra.tex`, Algebra Section 00JL, and checked the section's graded-module convention against the item's hypotheses: the ring and each module are direct sums of homogeneous additive subgroups, multiplication/action respects degree addition, and both maps preserve degree. I also searched the whole DAG and the blueprint for the item id and for graded-component exactness; the only use was the already existing dependent node, not an alternative statement of this item. A source search of `WeilConjectures/` and `Comparator/` found no declaration tagged with this item or stating it exactly.

Step 1 uses only the definition of exactness at the left end and degree preservation: an element of `A_n` whose image is zero is zero, so the restricted map is injective. Step 2 starts with a homogeneous element of `B_n` in the kernel, takes an arbitrary preimage supplied by exactness, decomposes it into finitely many homogeneous pieces, and uses degree preservation plus uniqueness of the direct-sum decomposition to retain its degree-`n` piece. Step 3 similarly decomposes a preimage of a homogeneous `c` and uses uniqueness in `C` to show its degree-`n` component maps to `c`. These are one-line direct-sum arguments, so all steps are marked elementary and there are no cited nodes or citation quotes.

I checked small cases while writing the statement-level proof: the zero exact sequence and the identity sequence `0 -> A -> A -> 0 -> 0` reduce each step to the corresponding direct-sum facts, and a sequence concentrated in one degree gives the ordinary exactness statement. No hypotheses were added or dropped, and no correction to the item's statement was needed.
