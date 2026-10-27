# Stage-1 report: lem-sfb-reduced-quasifinite-space-field-decomposition

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-reduced-quasifinite-space-field-decomposition.json: statement split in four steps; no Mathlib match for algebraic spaces.
- citations.json: eight verbatim quotations, one for every step/node pair.
- report.md: this report. searches.jsonl contains the actual required Mathlib searches run for this item.

No new nodes, hence zero new Mathlib leaves. The initial sandbox contained only dispatcher briefs, not an earlier node, report or search log. The live item was copied; its statement, source, statement dependencies, creation record, blueprint provenance and original Mathlib searches are retained.

## Attachments

None. Searching lean/WeilConjectures by the blueprint id, AlgebraicSpace, and reduced/quasi-finite terms gave no matching declaration. No upstream sorry declaration is counted as completed work.

## WANTED

None. All sources used are available in literature/stacks-project.

## Findings and changes

The imported statement is correct. Stacks 06S0, lemma-locally-quasi-finite-over-field, gives the locally Artinian finite-dimensional component classification without a reducedness assumption. Its proof explicitly passes through dimension zero, 06LZ and 06LH. Rather than introduce a duplicate 06S0 node, this split follows that passage using the existing lem-sfb-zero-dimensional-field-space-components. It then verifies that the given reduced atlas makes the represented scheme reduced and reduces the local Artinian factors to fields using the existing Mathlib leaf lem-sfb-reduced-artinian-residue-product.

The item had no proof or proof dependencies. These are now filled. The step citations use only the statements of existing nodes, not constructions hidden in their proofs. The schema has no hollow definitions and this delivery writes no Lean. Every step is below 800 characters, so no long step hides a lemma.

The inherited blueprint.from.node is null. The required blueprint_refs.py ancestor command reports None, consistently with the existing creation chain. I retained that provenance and its detailed place and via list, rather than inventing an ancestor. I read the current latest blueprint unit and its sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), and identified the subordinate field-space input in split_report.blueprint. Whole-blueprint searches for quasi-finite over a field, reduced locally quasi, Artinian local, and disjoint union of spectra revealed no exact imported blueprint node for the item. The existing created component-classification and ring nodes are reused.

## Mathlib searches

Ran the prescribed msearch.py for the item: LeanFinder with both the reduced locally quasi-finite space phrasing and the zero-dimensional reduced locally finite-type space phrasing; Loogle for AlgebraicSpace and LocallyQuasiFinite; grep for AlgebraicSpace/reduced quasi-finite/disjoint finite field in AlgebraicGeometry, plus the item's original broad grep query; LeanSearch for the reduced field-spectrum decomposition. All services answered. The logged hits were read: they concern schemes or rings, not representability and decomposition of an algebraic space, and no declaration specializes to the item in one line. The item therefore remains a split statement. No new nodes need searches. The original search records are retained, and each original query was actually run again in this sandbox.

## Not duplicates

No new nodes. In particular I reused lem-sfb-zero-dimensional-field-space-components instead of adding the 06S0 classification as a new node, and lem-sfb-reduced-artinian-residue-product instead of adding a reduced local Artinian field lemma. The field conclusion from the latter's singleton product is a short argument in step 4.

## Review by N0

I read Stacks spaces-over-fields.tex, Tag 06S0, statement and proof, and the cited dimension-zero representability passage Tag 06LZ, as well as varieties.tex Tag 06LH, statement and proof. Those sources impose local finite type and dimension zero, not quasi-compactness or an extra separatedness assumption. I also read the statements of every node used below and checked all eight literal quotations against those statements when writing citations.json. There are no new-node sources to review.

Step 1 uses lem-weil-pbc-lqf-locally-finite-type exactly for local finite type of each scheme chart. It uses lem-trf-locally-quasi-finite-relative-dimension-zero exactly for dimension zero of the field fibre of that chart. I read morphisms.tex Tag 0397 and the sentence after Tag 01TD saying local quasi-finiteness implies local finite type. The base is Spec k and its only residue field is k, so that fibre is the chart itself, with no extension-of-base-field issue. The dimension convention is expressly part of the statement of lem-sfb-zero-dimensional-field-space-components: the supremum of local dimensions calculated in etale charts. Thus its dimension hypothesis and its chartwise local finite type hypothesis hold. This argument also handles the empty chart and empty X by empty supremum.

Step 2 invokes precisely the conclusion of lem-sfb-zero-dimensional-field-space-components: representability, open-and-closed components Spec A_i, A_i nonzero local Artinian and finite-dimensional over k. I checked that its statement permits infinitely many components and the empty space. There is no circular dependency: a transitive read-only traversal of statement and proof dependencies of all seven cited nodes does not reach this item.

Step 3 retains the actual reduced etale atlas from the hypothesis, rather than silently assuming that an arbitrary atlas is reduced. After step 2 its target is a scheme. lem-weil-pbc-etale-smooth-zero-dimensional-fibres expressly says an etale scheme map is smooth; I use only that clause. The second assertion of lem-sfb-space-smooth-reduced-locality applies because the atlas is surjective and its source is reduced. I read its Stacks source 0GB3, lemma-reduced-local-smooth, which has exactly these hypotheses. On an open summand the stalks are the same local rings, so the equivalence in def-pc-reduced-scheme gives reduced global sections A_i. I read schemes.tex Tags 01J0 and 01J1 for that equivalence. There is no use of reducedness surviving arbitrary field extension.

Step 4 uses only the stated canonical product isomorphism and quotient-field clauses of lem-sfb-reduced-artinian-residue-product, with both Artinian and reduced hypotheses now verified. I read algebra.tex Tags 00J7 and 00JB, and Mathlib/RingTheory/Artinian/Module.lean lines 590-641, including equivPi at 633 and its component formula at 638. Nonzero locality means exactly one maximal ideal, so the product is a single field. Transporting its field structure to the same A_i preserves the existing k-algebra map and vector-space dimension. I wrote out why that unital map from the field k is injective. Keeping the same rings and maps makes the over-k isomorphism from step 2 the required one directly; no additional coproduct or scalar-compatibility theorem is concealed here.

The three off-unit scheme lemmas are declared in split_report.tool_uses with their exact uses: local quasi-finiteness implies local finite type, its relative dimension criterion, and etale implies smooth. These are generic tools for the chart calculation and reducedness descent; the constructibility unit's direct-image/alteration route is unchanged. I did not write maintainer-owned top-level tool_uses.

I checked delivery-errors B through E: statements introduce their objects and definitions; no new statement-only node or duplicated clause is created; all non-elementary facts have actual node citations; no dependency points back to the item; no source is an SGA source; there is no statement dispute or hidden change to hypotheses. Empty X gives empty I; an infinite disjoint union of Spec k is allowed; a finite purely inseparable extension is allowed and is not incorrectly claimed etale; the nonreduced test k[epsilon]/(epsilon^2) fails the input reducedness, exactly where step 3 needs it. No proof step assumes perfectness of k, finite cardinality of I, or separatedness before it is supplied by the classification.

## Unfinished work

None in this stage-1 split. The existing unsplit component-classification dependency remains its own queued item; this delivery does not split another worker's node. Required dry-run and push results are reported by the delivery command.
