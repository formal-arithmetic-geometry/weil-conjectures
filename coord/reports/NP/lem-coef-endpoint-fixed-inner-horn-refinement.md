# Stage-1 report: lem-coef-endpoint-fixed-inner-horn-refinement

## Files written

- `dag/nodes/sec-six-functors/lem-coef-endpoint-fixed-inner-horn-refinement.json`: existing statement, now split into seven steps; no Mathlib match for the entire assertion. The statement, statement dependencies, original source record, creation record, unit and blueprint ancestry are unchanged.
- `citations.json`: thirteen entries, one for each step/node pair, quoting the statements actually used.
- `searches.jsonl`: actual msearch log, retained with all results read; the new searches are also appended to the item's existing search records.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id and for inner horns, inner fibrations and Joyal returned no project declaration for this item. The upstream master id search also returned none; upstream reference material was not treated as proof evidence. The item has no existing Lean audit/declaration to attach.

## WANTED

WANTED: Lurie, Higher Topos Theory, Sections 2.2.5 and 2.4.6, especially Theorem 2.2.5.1, Lemma 2.2.5.2 and Corollary 2.4.6.5, archived under literature/, for lem-coef-endpoint-fixed-inner-horn-refinement. The original node already requests archival material. I opened the public [HTT PDF](https://people.math.harvard.edu/~lurie/papers/HTT.pdf) in the browser and read the model-structure statements at PDF pages 106–109 and the fibration criterion at PDF pages 154–155. No document was downloaded or added to the repository. The explicit relative construction is an agent proof, as recorded in proof_origin; its only external theorem inputs are existing DAG nodes.

## Corrections and source observations

The mathematical statement needs no correction. In particular, it does not require X to be a quasicategory or a to be a monomorphism. The additional hypothesis that r is an inner fibration is harmless: the proof only needs Y to be a quasicategory and the endpoint maps to be identities. I kept all original hypotheses.

The original source's Corollary 2.2.5.4 is a product-invariance statement, not the relative fibration criterion. The latter is HTT Corollary 2.4.6.5. The proof uses the exact existing interface `lem-coef-joyal-quasicategory-characterizations`, clause (1), and does not claim an inner fibration alone is a Joyal fibration. The source record is retained as inherited; this report corrects how its references are used.

The suggested main-20261015 file for the blueprint ancestor is absent in this local snapshot. I read the extant `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/prop-coef-integral-exceptional-adjoint.md`, including its paragraph beginning “For K”, and the current ancestor DAG proof. This item is a previously created technical refinement in that paragraph's coherent free-module/operadic-cylinder ancestry, not a claim that the blueprint itself states this simplicial theorem. `blueprint_refs.py ancestor` confirms the inherited ancestor. Blueprint searches for “inner horn”, “fibration”, and “endpoint”, together with whole-DAG searches for inner-horn refinements and Joyal interfaces, found no imported blueprint node stating this item in another form; same_as stays empty.

## Not duplicates

No new nodes were created. Existing general results were reused, specifically the Joyal model structure, its quasicategorical fibration characterization, and sectionwise presheaf colimits. The generic small-object factorization nodes do not themselves assert the required mixed-only countable cellular presentation; that presentation is constructed in the item's steps rather than shifted to a new node.

## Review by NP

I checked delivery-errors B–E against the statement and each proof step. There are no statement-only children to audit, no new definition, no relabelling of the conclusion as a new lemma, and no citations of proofs instead of statements. The mathematical inputs are the three original definition/model interfaces plus two existing theorem nodes. The quoted statements were opened before use. Each non-elementary step is at most 1294 characters; there is no step over 2000 characters. The compactness argument and lifting recursion are written out, not hidden behind an appeal to a standard small-object argument.

For step 1, `def-cbc-enhanced-diagrams-cones` supplies the explicit simplex and horn conventions; `lem-weil-pbc-presheaf-colimits-sectionwise` supplies the presheaf colimit assertion for sets, applied to the simplex category. I checked that its statement permits arbitrary small index categories and sets, not only abelian groups or sheaves. Coproducts, each pushout diagram, and the countable chain have small index sets; the displayed quotient constructions explicitly provide their set colimits. The endpoint condition on cells is imposed using the composite with r, so the construction is over the correct base. The source is the agent expansion of the ancestor paragraph, using this existing sectionwise-colimit theorem (whose source gives Stacks 00VB and 03CL).

For step 2, the same two statements justify degreewise pushouts and the concrete description of the horn. The set pushout argument shows injectivity even when the attaching map into the old stage identifies simplices. For a pure face, failure to belong to the inner horn would force all vertices except the missing interior vertex to have one endpoint value. Since vertices 0 and n remain, a monotone nonconstant interval simplex cannot have that form. This checks the potentially delicate mixed 2-simplex case, including repeated vertices. The pushout representatives may be chosen with all old elements unchanged, giving actual fixed endpoint objects rather than merely equivalences of fibres.

For step 3, `def-coef-infinity-fibrations` states exactly the inner-horn lifting condition used. The finite-stage factorization is proved using the finitely many generating faces of this particular horn; agreement on overlaps is reflected by the injections into the limit. No unproved compactness assertion about an arbitrary finite simplicial set is used. Constant-base lifting problems use the entire identity of simplicial endpoint fibres, not just their vertices. Step 4 then uses the quasicategory definition to fill the image horn in Y and the just-proved lifting property of k to lift it. X is never assumed fibrant.

For step 5, I checked the statement of `lem-coef-joyal-model-structure`: it asserts both that each inner horn is a trivial cofibration and that trivial cofibrations are exactly the maps lifting against all Joyal fibrations. The proof constructs those lifts recursively for the actual countable pushouts, taking their compatible colimit by the sectionwise-colimit node. This does not presume weak equivalences commute with arbitrary colimits and does not invoke a factorization of a that could change the endpoints.

For step 6, clause (1) of `lem-coef-joyal-quasicategory-characterizations` requires quasicategories on both sides, inner-horn lifting, and equivalence lifts with prescribed source. Those hypotheses are now available. The proof checks that an equivalence and its chosen inverse triangles in Y have constant interval coordinate. Since the endpoint fibre map is the identity, those same simplices give an equivalence in M with precisely the prescribed source and the prescribed image edge. Thus it supplies exactly what the cited statement requires, not just essential surjectivity on homotopy categories. This is also the content of the online HTT fibration criterion cited above.

For step 7, the Joyal model-structure node explicitly supplies two-out-of-three. It applies to the original equality a = k j and the categorical equivalences a and j, and combines with the fibration conclusion of step 6. The seven steps establish every clause of the unchanged item.

I tested empty X and Y, either endpoint empty, a pure one-endpoint target, the identity a, and non-injective a. In a pure target there are no mixed cells and a is already the endpoint isomorphism, so the construction returns the identity factorization. If an endpoint is empty, no mixed simplex can meet it. In general the set pushouts remain injective regardless of identifications made by a, and every equivalence remains confined to a single endpoint fibre. No SGA source or geometric detour is used.

The two Joyal theorem nodes belong to the item's own unit; the colimit theorem is already a Mathlib leaf and the remaining citations are definitions. No off-route theorem use needs a new tool-use declaration. I also checked the dependency closure of both Joyal inputs: neither reaches this item, so these citations do not introduce a cycle.

## Unfinished work

No part of the requested split is left unfinished. Archival acquisition is recorded above; no Lean work or compiler action was performed. The required dry run and push are the remaining delivery operations.
