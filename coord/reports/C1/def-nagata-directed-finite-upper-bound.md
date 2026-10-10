1. Files written

- `dag/nodes/sec-nagata-compactification/def-nagata-directed-finite-upper-bound.json`: existing definition marked split; no new nodes.
- `citations.json`: empty, because the definition has no proof steps.

2. Attachments

None. No declaration in `WeilConjectures/` carries the blueprint tag or states this selected recursive upper-bound function.

3. WANTED

None.

4. What was wrong or incomplete

The imported node had `same_as: null`, no statement dependency, no Mathlib searches, and no split report. I filled these fields. The only dependency needed for the statement is the generic notion of a nonempty directed index (`def-weil-directed-colimit-abelian-groups`); the selected function itself is custom. Mathlib search found only existential finite-upper-bound results such as `Finset.exists_le`, not this recursive choice, so the item is not a Mathlib leaf.

5. What could not be finished

Nothing remains for this definition. The surrounding approximation argument is explicitly marked bypassed in the blueprint.

## Review by C1

I read the item node, the `sk-prop-nagata-sketch-approximation` unit record, and the Nagata chapter record. I searched the complete project source for the blueprint tag and for the defining phrases; no declaration under `WeilConjectures/` matches. I also searched the blueprint for “selected common upper bound finite set” and “directed preorder”; the only result was the item itself, so `same_as` is `[]`.

The definition introduces a nonempty directed preorder, a base point, selected pairwise common upper bounds, and the Finset recursion. Its sole statement dependency is the existing generic directed-set definition, which supplies the meaning of the index notion; there are no proof steps and therefore no step citations. I ran LeanFinder, Loogle, Mathlib grep, and LeanSearch through `msearch.py`. LeanFinder returned existential upper-bound lemmas, Loogle and grep found no matching definition, and LeanSearch was unavailable; these results are recorded verbatim in `mathlib_searches`. Small cases are consistent: `u(∅)` is the fixed base point and `u({i}) = d(i_∅, i)` by the insertion clause. No new node was created, so there are no new-node statements or citation quotes to audit.

## Second reading by C1

- Item statement: checked against blueprint node order 328 and the approximation proof; the original insertion recursion was not well-defined for arbitrary pairwise choices, so the node now takes the finite-upper-bound function as data and states its required property.
- Proof steps: none; the node is a definition with no proof steps or citations to audit.
- New nodes: one existing split node, checked for B1-B7 self-contained form, TeX, imported-blueprint metadata, and absence of a Mathlib exact match; no new node files were added.
- Small cases: the repaired choice gives $u(\\varnothing)=i_\\varnothing$ and every singleton element is below its chosen value; empty and one-element finite sets introduce no additional assumptions.
- Mathlib searches: LeanFinder, Loogle, grep, and LeanSearch records were inspected; the first three found no exact selected-function definition and LeanSearch was unavailable.

### Source error

The blueprint's displayed formula used `\\nu` (a TeX Greek-nu command) where it intended `u`, and its claim that arbitrary pairwise choices define a Finset function by insertion is false: different insertion orders can produce different values when $d$ is not associative or commutative. The repaired node states the valid choice property used by the downstream lemma and records that insertion order is not part of the definition.

### Changes made

- Replaced the ill-defined pairwise recursion with a finite-subset upper-bound choice as explicit data.
- Corrected the `u` notation and supplied directedness and upper-bound conditions directly.
- Removed the unrelated `def-weil-directed-colimit-abelian-groups` statement dependency.
