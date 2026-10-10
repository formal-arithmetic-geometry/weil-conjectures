# Stage 1 report: lem-pc-tower-surjective-lim-acyclic

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-tower-surjective-lim-acyclic.json`: repaired item split with a three-step dimension-shifting proof; no new nodes.
- `citations.json`: verbatim citations for every node used by every step.

## Attachments

None. No sorry-free project declaration states the item exactly.

## WANTED

None.

## What was wrong and what changed

The returned version was circular: its second step applied the item's own surjective-tower acyclicity conclusion to the auxiliary Roos towers. I replaced that argument with the requested dimension shift. The existing `lem-pc-tower-injective-embedding` node supplies an embedding into a tower with injective levels and split-surjective transitions. The quotient tower is shown elementary to remain surjective. The existing inverse-limit exactness node gives surjectivity of `lim I -> lim Q`, and the long exact sequence node gives `R^1 lim B = 0` and `R^q lim B = R^(q-1) lim Q`; induction on `q` completes the proof. The horseshoe citation and `uses` list now both use `lem-sc-p1-right-derived-triangle-connecting`, as required by the return.

## Not duplicates

lem-pc-injective-split-tower-injective vs lem-pc-tower-surjective-lim-acyclic: the new node concerns injectivity of a tower with injective levels and split transitions; the existing item concerns vanishing of all higher derived limits for surjective towers.
lem-pc-injective-split-tower-injective vs lem-pc-tower-enough-injectives: the new node proves a sufficient condition for one tower to be injective; the existing node asserts only that the tower category has enough injectives.
lem-pc-injective-split-tower-injective vs lem-pc-tower-limit-left-exact: the new node concerns injective tower objects; the existing node concerns additivity and left exactness of inverse limit.
lem-pc-injective-split-tower-injective vs lem-pc-tower-abelian: the new node concerns injectivity under transition hypotheses; the existing node asserts that the tower category is abelian.
lem-pc-injective-split-tower-injective vs lem-pc-derived-limit-roos-abelian-groups: the new node concerns injective objects; the existing node computes derived limits by the Roos sequence and depends on the delivered item.
lem-pc-injective-split-tower-injective vs lem-pc-tower-injective-embedding: the new node states that a tower already having injective levels and split transitions is injective; the existing node constructs an embedding of an arbitrary tower into such a tower.
lem-pc-injective-split-tower-injective vs lem-pc-abelian-groups-exact-products: the new node concerns injective tower objects; the existing node concerns exactness of products of abelian groups.
lem-pc-injective-split-tower-injective vs lem-weil-pbc-mittag-leffler: the new node concerns injectivity in the tower category; the existing node concerns Mittag-Leffler exactness of inverse limits.
lem-pc-injective-split-tower-injective vs prop-weil-pbc-roos-triangle: the new node concerns injective tower objects; the existing node concerns a Roos triangle for derived limits in a different setting.

## Review by K1

I reread the item statement against Stacks Tag 07KW, Lemma 15.88.1 (3), including the category of towers, enough-injectives hypothesis, and the conclusion for every positive derived degree. I opened the complete statements of `lem-pc-tower-injective-embedding`, `lem-pc-tower-abelian`, the new `lem-pc-injective-split-tower-injective`, `lem-weil-pbc-tower-limit-exact-surjective-kernels`, `def-sp-left-exact-additive`, and `lem-sc-p1-right-derived-triangle-connecting`. Step 1 takes exactly the embedding and split-surjective transitions stated by the embedding node; the quotient transition is checked directly on representatives, and the short exact tower is justified by the abelian tower node. Step 2 uses the new injectivity criterion for `I`, the derived-functor definition for vanishing on the identity resolution, the exact-limit node for surjectivity of `lim I -> lim Q`, and the connecting node for the long exact sequence. Step 3 uses the same long exact sequence and the injective-resolution vanishing to identify the degree shift, then performs induction; it uses no Roos computation and therefore has no circular dependency.

I checked the surjective quotient argument on the zero tower and on a constant identity tower, and checked the induction at `q=1` and `q=2`. The existing embedding node was searched before adding anything. I added one statement-only node, `lem-pc-injective-split-tower-injective`, because the existing enough-injectives node did not state that the constructed split tower is injective; its source is the compatible lifting paragraph in Tag 07KW, and its LeanFinder, Loogle, and Mathlib grep searches found no matching theorem. The repair addresses return point D (circularity) and point C1/C5 (the text and `uses` now agree on the connecting-sequence node). Mathlib search records already present for the item were retained; no Mathlib leaf was introduced.

## Second reading by K1

- Item statement: checked against Stacks Tag 07KW, Lemma 15.88.1 (3), including the tower category, enough-injectives hypothesis, surjective transitions, and vanishing for every `q >= 1`; verdict: agrees hypothesis by hypothesis.
- Step 1: checked against `lem-pc-tower-injective-embedding` and `lem-pc-tower-abelian`; the quotient transition is explicitly lifted through the split surjection, and the short exact tower uses only the cited abelian-category statement; verdict: sound.
- Step 2: checked against `lem-pc-injective-split-tower-injective`, `def-sp-left-exact-additive`, `lem-weil-pbc-tower-limit-exact-surjective-kernels`, and `lem-sc-p1-right-derived-triangle-connecting`; the base case follows from surjectivity of the limit map and the long exact sequence; verdict: sound and non-circular.
- Step 3: checked against the long exact sequence and injective-resolution vanishing; the degree shift and induction are stated explicitly, with the `q=1` base supplied by Step 2; verdict: sound.
- New node `lem-pc-injective-split-tower-injective`: checked as a self-contained statement against the compatible-lifting paragraph following Tag 07KW; all notions have definition dependencies, TeX is written once, and semantic/grep searches are recorded; verdict: needed non-elementary node, not a duplicate or restatement.
- Edge cases: the zero tower and constant identity tower satisfy the statement; the induction was checked at `q=1` and `q=2`; verdict: no exceptional case found.
- Changes made: none to the node or citations; added this second-reading audit to document the checks required by sections B-E.
