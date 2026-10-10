1. Files written

- `dag/nodes/sec-picard-framework/lem-sp-cartan-eilenberg-properties.json`: repaired E7 by stating all six Stacks 015H Cartan--Eilenberg conditions inline; Mathlib searches found no Cartan--Eilenberg theorem.
- `dag/nodes/sec-picard-framework/lem-sp-cart-eilenberg-left-exact-cohomology.json`: statement-only child; Mathlib searches found no exact specialization.
- `citations.json`: verbatim statement quotes for every cited node in every item step.

2. Attachments

None. I searched both source checkouts by item id, Cartan--Eilenberg terminology, and likely declaration names; no sorry-free declaration states this item.

3. Source read

The Stacks source was read at `/home/ubuntu/c1-stacks-review/derived.tex`, lines 7105--7129 (Definition 015H and Lemma 015I), and lines 7177--7260 (Lemma 015J). The repository copy under `literature/` is not materialized, but the source checkout is available on this machine.

4. What was wrong or incomplete

The returned item was too weak: it referred to `thm-sp-if-e1`, whose statement does not grant Stacks 015H conditions (4)-(6), while the proof used them. I restated the CE resolution in the item itself with all six conditions after exchanging indices. Steps 1 and 3 now read those hypotheses directly and no longer cite the functorial CE node or `thm-sp-if-e1`; the left-exact comparison remains the separate unsplit child.

5. What I could not finish

The Stacks source file is not present in this checkout, so I could not inspect the original TeX lines directly; the split follows the imported Stacks-tagged statements and the existing reviewer note. The LeanSearch service was unavailable; Loogle, LeanFinder, and Mathlib grep were run and recorded.

## Review by K1

I reread the item and unit records, the Stacks 015H/015I source description, the double-complex definition, the left-exact/additive and injective-resolution definitions, and the returned functorial node to verify the mismatch. Step 1 now uses only the double-complex definition for indexing and differentials; all six CE clauses it invokes are written in the item hypothesis, including injective cycles, boundaries, and cohomology resolutions. Step 2 cites the child’s exact comparison statement and the left-exact/additive definition, with hypotheses supplied by clauses (4) and (5). Step 3 reads clause (6) directly and uses only the injective-resolution definition. I removed the old citations, proof dependencies, tool uses, and citation quotes for the functorial node and `thm-sp-if-e1`. The bounded-below/first-quadrant degree-zero edge case still checks, and the child remains statement-only without duplication.

## Not duplicates

lem-sp-cart-eilenberg-left-exact-cohomology vs lem-sp-cartan-eilenberg-properties: the child is the general left-exact comparison theorem for an arbitrary complex with injective cycles and boundaries, while the item specializes it to the vertical columns of a Cartan--Eilenberg resolution and also asserts the resolution property.

lem-sp-cart-eilenberg-left-exact-cohomology vs lem-weil-pbc-cartesian-eilenberg-functorial: the existing node defines the six Cartan--Eilenberg resolution conditions (and functorial lifts), while this child states the separate Lemma 015I comparison that a left exact additive functor preserves cohomology when cycles and boundaries are injective.

## Second reading by K1

- Item statement: checked against Stacks Definition 015H and Lemma 015I at `/home/ubuntu/c1-stacks-review/derived.tex:7105`; all six conditions and the exchanged indices agree, with the zero-complex and degree-zero cases consistent.
- Step 1: checked the transpose $I^{p,q}=C^{q,p}$ against Definition 015H and the double-complex indexing in `def-sp-double-complex-total`; the boundedness, row resolutions, and induced cycle/boundary/cohomology complexes follow clause by clause.
- Step 2: checked the hypotheses and comparison against Lemma 015I lines 7239--7258; the cited child states the needed split-cycle/boundary comparison, and the left-exact/additive definition supplies exactly the functor hypothesis.
- Step 3: checked the vertical-cohomology resolution against Definition 015H clause (6) and `def-sp-injective-resolutions`; the differential is the induced first-index differential.
- New node `lem-sp-cart-eilenberg-left-exact-cohomology`: checked against Lemma 015I and tested on a zero complex and a one-term complex; repaired the statement to define the abelian categories, cycles, boundaries, and cohomology explicitly.
- No Mathlib leaf: the recorded LeanSearch, LeanFinder, Loogle, and grep searches were rechecked in `searches.jsonl`; none states the Cartan--Eilenberg comparison.

Changes made: added explicit definitions of $Z^q$, $B^q$, and $H^q$ to the item and child statements to satisfy self-containment (B3); corrected the report's source note to the available Stacks checkout; no proof route or citation was otherwise changed.
