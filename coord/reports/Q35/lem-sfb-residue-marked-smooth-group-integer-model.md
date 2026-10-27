# Worker report

Item: lem-sfb-residue-marked-smooth-group-integer-model. Group: Q35. Date: 2026-10-24. Stage 1 only.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-residue-marked-smooth-group-integer-model.json — split into nine proof steps; statement unchanged; all twenty-one step citations checked against the cited statements.
- citations.json — one entry for each step/node citation, with the verbatim complete statement, including its hypotheses.
- report.md — this report. No new DAG nodes, no new Mathlib leaves, no Lean files, and no unit or chapter edits.

The sandbox also contains the genuine msearch.py searches.jsonl and a sandbox-only writing script. The live repository and launcher were read only.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, residue-marked and integer-model terminology, smooth/group descent, and the GroupScheme directory found no project declaration stating this item without sorry. The existing Mathlib declaration Algebra.Smooth.exists_subalgebra_fg is already represented by lem-weil-pbc-smooth-algebra-finite-type-model; it supplies the underlying smooth algebra only, not an attachment for the present item.

## Sources and searches

Read literature/stacks-project/algebra.tex, lemma-finite-presentation-fs-Noetherian (Tag 00TP), including its finite-coefficient construction, and limits.tex, lemma-directed-inverse-system-affine-schemes-has-limit (01YW), lemma-descend-finite-presentation (01ZM), lemma-descend-closed-immersion-finite-presentation (01ZP), and lemma-descend-smooth (0C0C). The proof uses the existing 00TP leaf instead of descending smoothness a second time. Read Mathlib/RingTheory/Smooth/NoetherianDescent.lean:214, Algebra.Smooth.exists_subalgebra_fg, confirming the existing leaf's exact specialization to the integer base.

Read the chapter record, unit record, SETUP's three levels, GOAL, the worker role, stage-1 brief and stage document, tools README, and both copies of delivery-errors sections B–E. Read the current literature/blueprint/latest (main-20261024) unit statement, direct-images proof (3), and the current thm-pd-spreading-out text. The current blueprint's formulations of morphism descent agree with the DAG formulation by its explicitly stated fibre-product universal property. No unit route is changed.

Whole-DAG source/tag and statement searches reused the smooth-model leaf, thm-pd-spreading-out, closed-immersion descent, affine qcqs and affine-limit results. tools/blueprint_refs.py searches for 01ZM, descent group, residue torus, smooth group and torus residue found no duplicate of the item. The 01ZM hit is the general spreading-out theorem used in the proof. The smooth group hit, thm-sc-theorem-of-the-base, is about Picard/Neron–Severi theory, not this statement. No new node is needed.

Fresh searches were run only through the required msearch.py command: LeanFinder with two phrasings, LeanSearch, Loogle for Algebra.Smooth.exists_subalgebra_fg, and grep for Hopf/group descent and exists_subalgebra_fg. Their actual queries and results are recorded, preserving all inherited Mathlib searches. The meaningful hits descend smooth algebras, not the marked group datum; none states the whole item.

WANTED: Brian Conrad, Reductive Group Schemes, Proposition 3.1.6, printed pp.83–84, for the historical integer-model reduction in lem-sfb-residue-marked-smooth-group-integer-model. The referenced PDF literature/conrad-reductive-group-schemes.pdf is not present locally. The supplied proof is explicitly agent-written from the available Stacks lemmas, not attributed to an unread Conrad proof. No SGA source is used.

## Issues found and corrected

The item was statement-only. Its statement is true as written and remains unchanged. A model of the underlying smooth scheme alone does not supply a group model; a torus merely isomorphic to the prescribed torus does not supply the required equality of parametrized maps. The proof now descends the actual operations, all five group identities, the actual marked map, its three homomorphism identities, and closedness in that order.

The residue-field limit is not the colimit of the quotient rings C/(C intersect p). It is the union of their fraction fields inside kappa(p). Step 5 explicitly includes both numerator and denominator in a finite subring and proves these inclusions injective. No coefficient field of A or separability assumption is used.

The inherited blueprint.from.node is null. The required ancestor command returns None because the long created.item ancestry terminates without an imported blueprint node. Its inherited detailed place and via list are retained; the report identifies the current direct-images proof (3) served by that chain. No invented ancestor or maintainer-owned field is added.

## Not duplicates

No new nodes. The existing 00TP, 01ZM, 01YW and 01ZP nodes are cited directly. Thus there are no new/existing same-tag pairs to distinguish.

## Generic tools from other units

The split_report.tool_uses names the affine smoothness dictionary, the existing smooth algebra Mathlib leaf, the algebra tensor pushout property, affine-limit and qcqs results, smooth base change, finite-presentation spreading out, and eventual closed-immersion descent. These are generic approximation and affine-geometry tools, not replacements for a step of the unit route. The use of lem-pc-proper-base-change is exclusively its smoothness clause (2).

## Review by Q35

I checked this split against the item and the sources, rather than treating the old source list as a proof. In step 1 the affine smoothness dictionary really states the equivalence needed in both directions, and the 00TP node really returns a finitely generated subring contained in A, a smooth algebra, and an isomorphism after tensoring with A. The tensor pushout node and affine-spectrum node justify the indicated scheme comparison by their universal properties. They are not cited for smooth descent or for a group law they do not supply.

In step 2 I checked directedness by finite unions of generators, the colimit by the actual union A, and the affine-limit node's explicit spectrum-of-colimit clause. The qcqs node applies because all bases and models are affine. Smoothness at enlarged subrings uses exactly clause (2) of the base-change node. The displayed polynomial presentations give finite presentation for powers, including the base and every source of a later identity; no noetherian or flat-transition assumption is slipped into a limit argument.

Steps 3 and 4 use the statement of thm-pd-spreading-out, clauses (2) and (3), respectively. It does not by itself assert descent of group schemes. I wrote the three operations, then the five associativity, left/right unit and left/right inverse equalities, with their finitely presented sources and common target. Common upper bounds handle finitely many maps and equalities. Fibre-product universality supplies pairing; the group definition supplies the precise identities being imposed. This also checks that the comparison alpha is a group isomorphism rather than just an underlying scheme isomorphism.

In step 5 the concrete fraction description follows from the residue-field definition: reduction of localization at a prime is the fraction field of the quotient domain. The contraction prime makes each quotient embed in A/p, so each fraction field embeds in k. Adding the numerator and denominator accounts for every element of k, with compatible inclusions. This is enough to reapply the affine-limit and qcqs statements over fields.

In steps 6 and 7 the morphism and equality clauses of the same spreading-out node apply to the torus and the fixed group model over kappa(p at C1). I checked finite presentation by the t_a u_a = 1 presentation and the group's already fixed finite presentation. The map being descended is the original i under the fixed alpha, not a new subgroup chosen up to isomorphism. The multiplication, inverse and identity comparisons have respectively the square of the torus, the torus, and the base as their sources. All three identities are imposed at a common field stage, and their exact statements survive further pullback.

For step 8 I opened the closed-immersion descent statement: it requires a locally finite type starting arrow and qcqs source, target and base, not merely finite presentation of some unrelated map. Here these are affine, and its target ring maps into a Laurent polynomial algebra generated by the finite list t_a and t_a^{-1} over the image. That proves the required finite type condition. The limiting map is the given closed immersion. Step 9 chooses exactly the ring index at which this property holds, so no additional unproved descent or closedness-under-base-change result is needed at the end. The original marking equality is retained at every pullback.

I tested r=0 (no torus variables, identity section), characteristic p and characteristic zero residue fields, nonmaximal primes, and nonreduced A. Nothing uses that A is a domain, that p is maximal, that A contains its residue field, that residue extensions are algebraic/separable, or that a group fibre is connected or reductive. The zero ring has no prime and does not occur among the hypotheses; empty underlying G is excluded by its identity over the nonempty Spec A. All proof steps are shorter than 2000 characters. No new-node definition, duplicate, disguised clause, or Mathlib-leaf audit remains. All twenty-one quotations were copied from and checked as substrings of the actual node statements. No compiler or Lake command was run.

## Unfinished work

No mathematical part of this split remains. The cited existing nodes retain their own independent proof obligations. Independent maintainer review follows the required dry run and direct delivery.
