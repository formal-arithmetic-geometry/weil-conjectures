# Q53 stage-1 delivery: lem-trf-general-nearby-slice-test

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-general-nearby-slice-test.json`: statement, split into four steps, not a Mathlib leaf. The statement is unchanged. The slice formula, comparison identification and all-slices detection are already in the more general existing `lem-trf-nearby-specialization-slice`.
- `citations.json`: nine verbatim statement quotations, one for each step/node citation.
- `searches.jsonl`: the five actual Q53 logged searches. The item's earlier Q77 searches are preserved as inherited records, not represented as Q53 searches.
- `report.md`: this report. `work/` holds the writing script and the local text extract from the ILO PDF, not additional delivery nodes.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag and for nearby-cycle, vanishing-topos, oriented-product, Milnor-tube and nearby/slice terminology; no project declaration states this item. No compiler or Lake command was used. The upstream master is reference material only, and was not treated as proof evidence.

## WANTED

WANTED: Fabrice Orgogozo, *Modifications et cycles proches sur une base générale*, section 1 and Lemma 3.1.1, for lem-trf-general-nearby-slice-test; local archival PDF `literature/orgogozo-modifications-cycles-proches.pdf` is absent. I read the author PDF online at https://www.cmls.polytechnique.fr/perso/orgogozo/articles/Modifications%20et%20cycles%20proches%20sur%20une%20base%20g%C3%A9n%C3%A9rale.pdf (printed pp. 2, 5–6). The read-only literature list was not modified.

## What was wrong or incomplete

The item had no proof and no Lean attachment. It overlaps an existing, more general node: `lem-trf-nearby-specialization-slice` treats any coefficient ring killed by an integer and bounded-below K, gives the ordinary comparison compatibility for arbitrary T, and tests cohomology vanishing of arbitrary derived objects. Rather than reproduce that existing node as new clauses, this split uses it and proves explicitly how to pass from comparisons to their cones. No new slice theorem is introduced.

In the vanishing criterion, “every such sliced comparison” ranges over all choices of geometric specialization on T, with its image specialization on S, not just lifts of one fixed pair on S. The proof makes this quantifier explicit; the item statement is unchanged. A fixed slice does not generally give a conservative family.

There is a minor source-index typo in the author's p. 6 pointwise explanation: it prints the left oriented stalk as `(x_S,a_S)`, whereas the displayed j-map and the introductory Milnor-tube formula require `(x_S,b_S)`. The imported item and the reused general slice lemma use the correct j-map from S_(b), so no correction to the item's statement was needed. The proof never replaces S_(b) by the geometric point b.

## Route and searches

Read `AGENTS.md`, `roles/worker.md`, the stage-1 brief and stage document, SETUP's three levels, GOAL, STATE, dag-sync, tools/README and delivery-errors B–E. Read the chapter and unit records and the current main-20261015 local-term proof and unit. This is an auxiliary slice calculation in the existing normal-cone/Orgogozo route of `lem-trf-local-term-locality`, through the inherited blueprint ancestry; neither the chapter nor unit route changes.

Ran `tools/blueprint_refs.py ancestor lem-trf-general-nearby-slice-test` and searches `nearby`, `specialization`, `slice` over all imported blueprint nodes. None states this item; same_as remains []. Searched the whole DAG by oriented/vanishing/slice terminology and read the neighboring strict-local, geometric-trait-slice, point-cohomology, points-conservative and general specialization-slice statements. The trait geometric slice has different generic-side input; the arbitrary-specialization node is the correct reusable interface.

The five Q53 `msearch.py` searches and actual results are retained in searches.jsonl and appended verbatim to the item's search records: Loogle `"nearbyCycles"` and the nearby/vanishing/Milnor grep had no hits; LeanSearch and two differently phrased LeanFinder queries returned ordinary topological or scheme stalk-specialization statements, structure-sheaf restrictions, global sections, or specializing-map facts. I read the displayed signatures: none has the oriented nearby-cycle or comparison-cone conclusion. All services completed successfully; no unavailable search is recorded as a negative result. No Mathlib leaf was asserted.

## Not duplicates

No new nodes. In particular the existing `lem-trf-nearby-specialization-slice` is reused as a genuine generalization, rather than cloned. The cone passage is a short application of existing exact-functor and derived-category statements, not a new lemma node.

## Review by Q53

I read Orgogozo's author PDF section 1 (printed p. 2), section 3.1 (printed p. 5), and the first proof paragraph and first sliced display of Lemma 3.1.1 (printed p. 6). The display has the strict-local generic side, arbitrary T, the ordinary comparison, and a cone with the stated degree bound; the preceding paragraph explains why a preliminary base change is quantified separately. I also read the local ILO Exposé XI 1.4, 1.8–1.9, 2.2–2.3, 2.7, and 4.3 (printed pp. 172–185). Those passages corroborate the oriented point convention, specialization section, functoriality and nearby-cycle definition. No prohibited SGA source was used. For the exact-functor tools I read Stacks `homology.tex` Tag 010N (`lemma-exact-functor`) and `derived.tex` Tag 015F (`lemma-right-derived-exact-functor`); these are the correct labels and tags, not mutable section numbers. There are no new nodes needing independent source review.

Step 1 uses the actual statements of `def-weil-finite-type-morphism`, `def-trf-oriented-nearby-cycles`, and `lem-weil-pbc-exact-functor-complex-cohomology`. The first supplies finite affine finite-generation charts, the second says the constant-coefficient pullback is exact and termwise, and the third says precisely that cohomology commutes with an exact functor. I checked that scalar extension preserves the given finite generators and cover, exact pullback preserves the same uniform cohomology bounds, and an invertible integer stays invertible after base change. Thus the bounded-below hypothesis of the reused lemma holds on all bases. This is a few-line specialization of the cited statements and definitions, so the step is marked elementary. It adds neither properness nor Noetherian hypotheses.

Step 2 uses `lem-trf-nearby-specialization-slice` and `def-trf-oriented-nearby-cycles`. I opened and read their complete statements: the lemma gives exactly the geometric slice morphism and i-star/Rj-star isomorphism for the same strict localizations, as well as identification of the ordinary comparison for every T and compatible pair. This is a statement clause, not material extracted from that lemma's proof (which is empty). The definition specifies beta as the counit mate. D^b is contained in D^+, and the coefficient ring killed by an invertible integer meets the weaker annihilator hypothesis of the lemma. I did not infer that any ordinary comparison is invertible.

Step 3 uses `lem-trf-nearby-specialization-slice` for exactness of e-star, `lem-sf-exact-functor-derived-triangulated` for the triangulated functor on the entire derived categories of arbitrary abelian categories, and `def-weil-abstract-derived-category` for the distinguished cone triangle and its explicit matrix differential. The module sheaf categories are abelian, and exact constant-coefficient inverse image meets the functor hypothesis. I checked the degree-q cone term B^q plus A^(q+1), its signs, and its image under the additive termwise functor. There is no shift of the cone and no lowering of r. A cone is used only up to isomorphism; no unjustified functorial cone in the triangulated category is chosen.

Step 4 uses the final statement clause of `lem-trf-nearby-specialization-slice`, which explicitly tests all cohomology degrees i <= r of an arbitrary object A on V_f, not merely isomorphisms or H^0. Apply it to f_T and A=C_g; step 1 supplied finite type of f_T. The same lemma explicitly includes compatibility under successive base changes. Every slice over T maps to a specialization pair on S, so the family in the step is the whole conservative family, not one fixed pair. The cone identifications from step 3 then prove both directions. No boundedness of the cone beyond what this criterion states is required.

I checked B1–B10: no new unfinished nodes or duplicate notions, no phantom Mathlib match or attachment, all symbols retain their definitions, TeX has single mathematical escapes in decoded JSON, the blueprint ancestry is preserved and same_as was searched. For C1–C8 I checked each non-elementary inference against a cited statement, copied a substantive verbatim quote for every citation, and traversed both statement and proof dependencies of the three theorem tools: none reaches this item. The general slice theorem is in the same unit; the off-unit homological tools are already Mathlib leaves, so no unapproved route replacement or tool-use declaration is needed. D1–D5: no clause is moved into a new node, and the short cone argument is written out. E1–E7: every object/hypothesis matches, there is no tensor-flatness or hidden proper base-change assertion, and no source statement error was reproduced.

Small cases checked: X empty and Lambda the zero ring give zero complexes and vacuous/zero cones; K=0 also does. Identity g gives the identity counit-mate comparison and zero cone on both sides. A punctual base reduces the slices to the usual fibre restriction. For a trait the formulas still use the strict localization at b, not a geometric generic fibre; these are different formulas in general. Negative r is allowed without index changes. Arbitrary non-Noetherian T is permitted because the reused lemma has no such restriction. No statement was weakened. All four non-elementary/elementary steps are under 2000 characters; the cone calculation is a routine application, not a hidden independent comparison lemma.

## Unfinished work

No part of this one-level split remains unfinished. The existing general specialization-slice node remains its own independent stage-1 task and is not silently marked proved here. The required server dry run and push are performed after writing this report; their results are recorded below when available.
