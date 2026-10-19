# Worker report

## Files written

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-derived-stalk-conservative.json`: statement, split; no new nodes and no new Mathlib leaves.
- `citations.json`: eight entries, one per citation in the three proof steps.
- `report.md`: repair report. No unit, chapter, Lean, or live-project file is delivered.

## Attachments

No attachment for the item was found by searching `WeilConjectures/` in the read-only slopmaster2 source for its blueprint tag and for derived/stalk conservativity. `AlgebraicGeometry.Scheme.isIso_of_isIso_sheafFiber_map` belongs to the existing node `lemma-weil-pbc-geometric-stalk-conservative`, not to this derived criterion. I read that declaration at `WeilConjectures/Mathlib/AlgebraicGeometry/Sites/EtalePoint.lean:173`; it reflects isomorphisms of sheaves, and the existing node's audit records it closed.

## Literature

No WANTED documents. I read the item's master-blueprint statement and three proof paragraphs, `dag/chapters/sec-curve-estimates.json`, and `dag/units/sk-prop-cd.json`. For the abstract derived-category argument I read `literature/stacks-project/derived.tex`, Tag 05RT, label `lemma-acyclic`, and Tag 05RU, label `definition-unbounded-derived-category`; the local tag table confirms both labels. These give localization at quasi-isomorphisms and cohomology functors on the localization. The existing Mathlib leaf `lem-pc-quasi-isomorphisms-multiplicative-system` supplies the calculus of fractions explicitly.

## What was wrong and what changed

The return names `status: imported, not split` as the failing check. The other phrases, `proof written by an agent` and `unit sk-prop-cd has no realization recorded yet`, are notes in `tools/review_split.py`, not failure conditions. The item is now explicitly `status: split`. The mandated delivery tool fetches the current origin baseline and overlays the sandbox's owned fields, preserving maintainer fields; the final dry run therefore packages the repair on the current DAG rather than re-pushing the old commit.

This item is not the key node of `sk-prop-cd`: that unit asserts high-degree cohomological vanishing on curves, whereas this lemma asserts derived stalk conservativity on arbitrary schemes. I leave its realization unchanged. Assigning this lemma as a realization of the curve-vanishing statement or its six proof steps would be false bookkeeping.

I also corrected a substantive C4 weakness in the earlier split: the definition of localization alone was quoted as if it stated an isomorphism criterion. Step 1 now writes both directions and cites the existing abstract derived-category definition, including its cohomology-factorization clause. For an arbitrary derived morphism it uses the existing calculus-of-fractions node and explicitly writes the roof, the cohomology equation, and the inverse. This avoids conflating a derived morphism with a single chain map.

In Step 2 I removed the unnecessary appeal to exact stalks commuting with cohomology. The statement already displays the stalks of cohomology sheaves, so ordinary sheaf conservativity applies directly. In Step 3 I wrote the inverse after applying cohomology and stalk functors; preservation of identities and composition gives the two inverse equations. No statement clause or hypothesis was changed. Every step now has a source field. `proof_origin.by` remains `agent`, since this is a synthesis using the blueprint and existing source facts, rather than a falsely claimed verbatim literature proof of the whole item.

## Review by NR

I reopened all current cited statements, not their proof bodies: `def-weil-pbc-derived-categories`, `def-weil-abstract-derived-category`, `lem-pc-quasi-isomorphisms-multiplicative-system`, `def-weil-pbc-etale-sheaves`, `lemma-weil-pbc-geometric-stalk-conservative`, and `def-weil-pbc-geometric-stalks`. Their statements are identical in the fetched clone and the read-only live DAG mirror. I also read the exactness node used by the old split; it remains a Mathlib leaf, but is no longer a proof dependency because its exactness assertion is not needed.

For Step 1, the derived-category node explicitly defines the coefficient-free category as the derived category of abelian etale sheaves and defines D-plus as a strictly full subcategory. The abstract-derived-category node explicitly defines quasi-isomorphisms by all cohomology maps, localizes at them, and states that the cohomology functors factor through Q. These clauses justify localization sending quasi-isomorphisms to isomorphisms and the reverse implication by applying cohomology to an inverse. The fractions node states both left and right calculi for the same class in the homotopy category of any abelian category, with D(A) as that localization. Thus the roof used in the step has exactly the required quasi-isomorphism denominator. The intermediate roof complex need not have bounded-below terms: the calculation takes place in D(A), and the inverse is a morphism of D-plus because that subcategory is full. No boundedness hypothesis is added.

For Step 2, the etale-sheaves definition gives the abelian sheaf category, the derived-category definition places each cohomology sheaf in it, and the stalk-conservativity node states exactly the iff for morphisms of those sheaves at every geometric stalk. Apply it separately to each integer degree; Step 1 then gives invertibility. No exactness, finite-type, properness, torsion, or constructibility assumption is used or introduced.

For Step 3, the abstract-derived-category definition supplies the functors H^i. The geometric-stalk definition supplies the colimit of sections over pointed etale neighbourhoods. A sheaf morphism and its inverse give inverse maps on every section object and hence inverse colimit maps. This is an elementary functoriality calculation, explicitly written in the step; no new exactness or homology comparison lemma is hidden there.

I regenerated citations.json with the complete verbatim statements of the cited nodes so each quote includes the actual clause used, correcting the old quote for exactness that only named the functor. The citation list agrees with the union of step uses. I checked B through E against the files: no new nodes to satisfy B1/B2 or test for duplicate Stacks tags; the statement is self-contained in its original scheme, category, degree, and point hypotheses; definitions are cited; TeX has ordinary JSON escaping; inherited Mathlib searches are retained from searches.jsonl, with service failures recorded unavailable. No new search was claimed. The whole-DAG search found and reused the existing localization/fraction facts, so no restatement node was introduced. The only cross-unit statement tool added is already a Mathlib leaf and is allowed without a new tool-use approval. The proof uses no cited node's internal proof and makes no induction or new existence choice.

Small cases: for zero complexes and degrees with zero cohomology, every relevant map is the unique map of zero objects and the criterion holds. On the empty scheme, stalk hypotheses are vacuous and sheaf conservativity correctly makes every abelian sheaf map invertible. A field scheme and a nonzero shifted sheaf retain every integer degree; there is no accidental degree-zero restriction. These checks concern the item; no new statement needs a separate small-case test.

## Not duplicates

No new nodes were created. Existing general facts were reused; no clause of the item was moved into a new node.

## What remains

Nothing unresolved for this stage-1 split. The unit's unrelated curve-vanishing realization is outside this item's scope. This worker does not push: a fresh second reader must review the repaired sandbox and deliver it.

## Second reading by NR

- Item statement: checked against the blueprint node and its three clauses; the scheme, bounded-below derived objects, all integers, and every geometric point are present, with no added hypotheses.
- Step 1: checked against the abstract derived-category, derived-categories, and calculus-of-fractions node statements; the roof argument uses only their stated localization and factorization properties.
- Step 2: checked against the etale-sheaves definition, derived-categories definition, and geometric-stalk conservativity statement; stalks are taken on cohomology sheaves directly, so no unstated exactness claim is used.
- Step 3: checked against the abstract derived-category cohomology functors and geometric-stalk colimit definition; identity and composition preservation supplies the stated inverse maps.
- New nodes: none; therefore B1--B7, duplicate checks, and small-case checks introduce no additional node obligations.
- Small cases checked: zero complexes, a field scheme, and the empty scheme; the criterion remains correctly formulated (vacuous stalk condition on the empty scheme).
- Confirmed the imported item must retain `blueprint.from = null`; the delivery preflight explicitly requires this for blueprint-imported nodes.
- No mathematical statement, proof step, citation quote, dependency, or metadata was changed.
