# Stage-1 report: lem-sfb-scheme-derived-etale-qcoh-comparison

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-derived-etale-qcoh-comparison.json: item split, statement unchanged, no Mathlib match.
- citations.json: every citation in all three proof steps, with verbatim statement quotes.
- searches.jsonl: actual msearch.py queries and results, retained alongside the item.

New nodes: 0. Mathlib leaves: 0. No Lean written and no compiler or build invoked.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, Zariski/etale comparison terminology and derived quasi-coherent comparison terminology. No project declaration states all clauses. The existing DAG theorem is material to cite, not an attachment to a finished Lean proof.

## WANTED

None. The Stacks sources needed here are present locally.

## Findings and corrections

The item was statement-only. The existing lem-sfb-derived-etale-zariski-equivalence is strictly stronger: besides this item's equivalence, structure modules and qcqs direct images, it specifies arbitrary derived pullback comparisons and their normalization/coherence. Reusing its statement avoids duplicating the long proof of Stacks 071Q. The item retains its exact statement. Added statement dependencies for the mentioned K-injectives, K-flats, size convention and unbounded derived global sections. No definition is changed.

The inherited blueprint ancestor is null: tools/blueprint_refs.py ancestor reports None. The inherited from.place is already specific and was retained, together with its full via list. I read the latest blueprint's direct-images proof (3), the chapter record and the unit record: this auxiliary coherent-coefficient comparison supplies a construction below the existing proper-flat-space-duality route; it does not replace the constructible six-functor argument. Blueprint searches for derived-etale-zariski, 071Q and cohomology-over-U-trivial had no results; searches for quasi-coherent and Zariski were inspected. Whole-DAG tag searches found and distinguished the existing comparison and affine-realization nodes. No new node or new blueprint identity is required.

## Not duplicates

No new nodes. lem-sfb-scheme-derived-etale-qcoh-comparison is handled by specialization of existing lem-sfb-derived-etale-zariski-equivalence plus the explicit derived-global-sections calculation. I do not create a replacement node for any clause of the item.

## Review by Q50

I read spaces-perfect.tex Tag 071Q (lemma-derived-quasi-coherent-small-etale-site), its full proof, and the preceding flatness lemma 08H8. I also read Tag 08GH (remark-match-total-direct-images), including both squares and the argument using the inverse equivalences. These sources apply to unbounded complexes; the equivalence needs no quasi-compactness hypothesis. The qcqs assumption occurs precisely in the direct-image clause. I read derived.tex Tag 08BJ (lemma-adjoint-preserve-K-injectives), including its short homotopy-category adjunction proof. No SGA route is used.

For step 1 I opened lem-sfb-derived-etale-zariski-equivalence and checked that its statement asserts exactness on all module sheaves, the D_QCoh equivalence with the canonical unit/counit and R epsilon_* as inverse, and identification of structure modules. Its notion of quasi-coherence is exactly the one used here; its extra size convention is a universe choice, not a geometric hypothesis. The multiplication map b tensor a to ba and b to b tensor 1 explicitly give the unit-module normalization.

For step 2 I checked the same node's direct-image clause word for word: it applies to quasi-compact quasi-separated scheme morphisms, not merely separated ones, and intertwines the unbounded derived direct images under the canonical ringed-site comparison. Thus specialization h=v gives every requested clause. I do not use the underived comparison node's separated hypothesis for a qcqs-only morphism. There is no hidden finite-type, noetherian or boundedness hypothesis.

For step 3 I opened prop-pur-kinjective-resolutions-exist and checked that it provides an unbounded, degreewise-injective K-injective resolution for modules on a small ringed site. Both sites can be chosen small relative to their module universe as the comparison theorem explicitly requires. I opened def-pur-kinjective-complex: it says exactly that maps from acyclic complexes are null-homotopic. The argument writes out the adjunction on chain maps and homotopies and uses the exactness already supplied by step 1. It therefore proves, in a few lines from those definitions, the preservation assertion needed for epsilon_*I; it does not assume it from a definition. Finally I opened def-pur-ringed-site-zeroth-hypercohomology and checked its definition of the unbounded R Gamma via K-injectives. Both R Gamma values are represented by the identical complex of values on the final object. The unit from step 1 gives the desired derived isomorphism, not merely degreewise equalities. Identity of representative maps gives naturality. This is an elementary application of the explicit 08BJ argument, not a new auxiliary node.

Edge cases checked: the empty scheme, the zero complex, arbitrary shifts, and schemes that are not quasi-compact. The first three yield the same zero or shifted representative complexes. The last requires no structural morphism to an affine base be qcqs: the final-object/K-injective calculation proves the global-sections assertion directly. Thus the final clause has the same generality as the equivalence. For v an identity, the canonical comparison is the identity. A qcqs but non-separated v remains covered by step 2's cited statement.

I checked delivery-errors B through E against the files: every cited statement was opened, every non-elementary input is cited, no new clause-restatement node was created, the original statement and route are preserved, and the dependency closure of every cited theorem/definition excludes the item. Each proof step is below 2000 characters. The only off-unit theorem is the general K-injective existence input, declared in split_report.tool_uses with its purpose. Search records were appended only for actual msearch.py invocations; the prior inherited searches are retained as required. I read all returned hits: dense-subsite/sheaf equivalences are not this module comparison, and the quasicoherence data/etale morphism hits supply neither the derived equivalence nor its direct-image clause.

## Unfinished work

None in this stage-1 split. Existing cited unsplit nodes remain separate queue items; I do not write their Lean or split them here.
