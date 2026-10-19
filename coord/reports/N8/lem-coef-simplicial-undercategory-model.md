# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-simplicial-undercategory-model.json`: statement, split into twelve explicit verification steps; unchanged statement. Mathlib verdict: no match for the full simplicial undercategory theorem. No new nodes and no new Mathlib leaves.
- `citations.json`: one entry per step/node citation, each with a verbatim excerpt of that node's statement.
- `report.md`: this report. `write_split.py` is a sandbox-only preparation script, not a delivery file.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` by the blueprint tag, undercategory, coslice, simplicial-model and ModelCategory/Under terminology. There is no project declaration stating the item. Also checked the corresponding master terminology as reference only, without treating a master declaration as finished evidence.

## Wanted sources

WANTED: Jacob Lurie, Higher Topos Theory, Definition A.3.1.5, Remark A.3.1.6 and the proof of Lemma A.3.7.1 (printed pp. 851-852 and 907), for lem-coef-simplicial-undercategory-model. Read the PDF online at https://people.math.harvard.edu/~lurie/papers/HTT.pdf; it is not archived in the repository. No Stacks tag states the simplicial undercategory construction. No download or literature change was made.

## What needed completion

The item was a correct statement-only auxiliary node. Its source invokes the simplicial model category of objects under A, without constructing it. The split now constructs it and verifies the axioms. In particular, ordinary undercategory colimits are not always underlying colimits: the proof uses the pushout of the underlying colimit and A over the colimit of the constant A diagram. The empty diagram and a disconnected diagram therefore cause no failure. This is a check on a possible proof error, not a change to the item statement.

The existing blueprint ancestry and its complete via list are preserved. I read the chapter, unit and current main-20261015 proof of prop-coef-integral-exceptional-adjoint; its second paragraph is the coefficient-adjunction calculation served by this established auxiliary chain. The unit's key node is not this item, so no unit record changes. No route change, coefficient-category identification, target change, SGA source, or new definition is involved.

## Search and duplicate checks

Ran blueprint_refs.py ancestor and searches for `undercategory`, `simplicial model`, and `coslice`; no imported blueprint node states the item. Searched the whole DAG for those concepts and the source identifiers A.3.7.1, A.3.1.5 and A.3.1.6. The existing local-mapping-test node uses this theorem; it does not state the construction, and the Reedy, pointed-model, lifting-class and infinity-coslice nodes concern different structures. No additional node is needed because the proof consists of explicit universal-property and model-axiom verifications.

The six fresh Mathlib searches were all run through the required msearch.py command and are recorded verbatim by tool and query in the item, retaining all inherited records. Both semantic phrasings were read. The significant hit, HomotopicalAlgebra.ModelCategory.over, is only an ordinary overcategory theorem (Over.lean:143-145); line 26 explicitly leaves Under as TODO. The other semantic hits concern simplicial objects or the monoidal closed structure on simplicial sets. I read SimplicialCategory/Basic.lean:19-30 and SimplicialCategory/SimplicialObject.lean:34-41: neither supplies the asserted model-compatible undercategory tensor, cotensor and strict-fiber enrichment. Thus this is neither an attachment nor a Mathlib leaf.

## Not duplicates

No new nodes; no new/existing pairs need separation.

## Review by N8

I read the complete item, the current blueprint ancestor's proof, and HTT's definition/SM7 formulation and undercategory invocation online. Because the cited document is not archived, proof_origin is agent, and each proof step states its explicit verification rather than passing off the invocation as a proof. There are no new-node sources to check. I reviewed delivery-errors B-E against the final statement, steps and citations.

I opened the full statements of lem-coef-simplicial-model-nerve-localization, def-weil-pbc-category-colimit and lem-coef-kan-quillen-right-proper before citing them. The first explicitly supplies the complete/cocomplete model-category conventions, functorial weak factorization systems, enriched tensor/cotensor structure and SM7, not just a localization assertion. The second supplies exactly the cocone universal property. The third explicitly supplies horn and boundary characterizations of fibrations and trivial fibrations. No conclusion is taken from their proofs or from their titles.

For step 1, completeness and the universal property of a limit construct the arrow from A; testing after every projection proves the lift is under A, including when the index is empty. For step 2, cocompleteness from the convention node and the colimit definition give the displayed pushout construction. I checked that equality on B is tested on its coprojections even for empty or disconnected indices; I did not assume a connected index or that the forgetful functor preserves all colimits. Step 3 uses only the retract and two-out-of-three axioms explicitly stated by the convention node, after forgetting an actual retract diagram.

For step 4, I checked both factorization classes and the intermediate arrow la from A, and verified that a functorial map of factorizations respects it. Step 5 uses the ground diagonal lifting axiom only with its exact cofibration/trivial-fibration or trivial-cofibration/fibration hypotheses, and the equation ha'=hia=ua proves the diagonal lies under A. Step 6 writes the two retract diagrams explicitly, so the mutually characterized lifting classes required in the definition of a weak factorization system really have been established. Step 7 uses the convention node's exact definitions of cofibrant/fibrant; it does not assert that the underlying target of a cofibrant under-object is cofibrant.

For step 8, I checked enrichment in every simplicial degree, including closure of composition, identities and simplicial operators, and verified that degree zero is the ordinary category in the statement. Steps 9 and 10 use the tensor/cotensor assumptions explicitly present in the convention node. I expanded why tensoring by a simplex preserves the pushout using the cotensor adjunction, and why exponentiation preserves the required pullback using the cartesian exponential adjunction. The resulting isomorphisms are of simplicial sets and natural, not merely bijections of vertices. In particular the tensor glues along A tensor K and collapses that factor to A; the cotensor uses constant maps from A.

For step 11, the cofibration and fibration hypotheses in the undercategory are exactly the ground hypotheses needed by the convention node's SM7 sentence. I checked the pullback identification degree by degree: restriction of fi along a forces f to restrict along a' to b, and conversely the latter condition gives both target restrictions. Step 12 cites the Kan node for the horn/boundary characterizations only, and writes the proof of pullback stability of their lifting properties. No right properness theorem or homotopy-fiber comparison is used. These checks also show precisely why no cofibrancy of A is needed.

Small cases checked: A initial recovers M, its original mapping simplicial sets and its tensors/cotensors; K empty gives the initial under-object 1_A as tensor and the terminal under-object A to 1 as cotensor; K a point recovers the original objects. The empty diagram produces initial 1_A and terminal A to 1; a two-object discrete diagram produces X coproduct_A Y, as it should. The mapping fiber for source 1_A is the one-point simplicial set. The SM7 pullback does not require Map(A,Y) to be Kan, so a noncofibrant A causes no hidden hypothesis. All these tests agree with the unchanged statement.

Checked the dependency closures of both model convention and Kan nodes and the colimit definition: none reaches the item, so the proof introduces no cycle. The twelve proof steps have complete boolean elementary flags; steps 11-12 are non-elementary applications of the cited SM7 and Kan results, while steps 1-10 are written-out definition/universal-property verifications. proof_deps is exactly the union of uses. Every step/node entry in citations.json was checked as a literal substring of the corresponding statement. No citation is an uncited theorem by tag.

## Unfinished work and validation

No mathematical clause is deferred and no new unsplit nodes were created. The required validation is `python3 /home/ubuntu/weil-launcher-nt/deliver.py N8 lem-coef-simplicial-undercategory-model --no-push`; the second reader must deliver after reviewing this sandbox. This worker does not push.

## Second reading by N8

I independently read the item and all twelve steps, the complete statements of its three cited nodes, Stacks `categories.tex`, label `definition-colimit` (002F), and HTT Definition A.3.1.5, Remark A.3.1.6 and the proof of Lemma A.3.7.1 at printed pp. 851-852 and 907 (PDF indices 868-869 and 924). The HTT proof invokes the simplicial undercategory; it does not prove the construction, so the explicit construction correctly remains marked agent-written. No Stacks tag states the item. I also read the current main-20261015 ancestor proof's second paragraph, the chapter record and the recorded unit. Its derived coefficient-adjunction calculation is the inherited ancestry; this split does not change that route.

Statement: PASS against the HTT invocation and the expanded axiom verification. Every ground model axiom is in lem-coef-simplicial-model-nerve-localization's statement, and the inherited classes, strict fiber, pushout tensor, constant cotensor, initial/terminal objects and objectwise fibrancy/cofibrancy all have the asserted types. Neither SM7 nor the factorization/lifting constructions require A cofibrant, properness or combinatoriality. No statement dispute or correction is needed.

- Step 1: PASS against the convention node's completeness: limit uniqueness proves the under-A condition, even for an empty index.
- Step 2: PASS against completeness/cocompleteness and the exact cocone universal property in def-weil-pbc-category-colimit, also checked against Stacks 002F, label definition-colimit: B is the colimit of constant A, not A; the pushout proof covers disconnected and empty diagrams.
- Step 3: PASS against the convention node's retract closure and two-out-of-three: forgetting really preserves the requisite diagrams and compositions.
- Step 4: PASS against both functorial factorization systems in the convention node: the new source arrow is la and rla=b; the functorial middle map preserves it.
- Step 5: PASS against those systems' lifting axioms: the equation ha'=hia=ua=b proves every chosen ground lift is under A, in each of the two class pairs.
- Step 6: PASS against the weak-factorization definition and step 3: both displayed pairs of arrow maps compose to the appropriate identity and exhibit the stated retracts; step 5 makes them arrows under A.
- Step 7: PASS against the convention node's initial/terminal-map definitions: cofibrancy tests a itself, and fibrancy tests X to 1, without asserting X cofibrant.
- Step 8: PASS against the ground enrichment: constant n-simplices are closed under composition, identities and all simplicial operators, and vertices recover exactly the ordinary undercategory.
- Step 9: PASS against the ground enriched tensor/cotensor adjunctions: tensor by each simplex preserves the pushout by the written adjointness argument; its mapping fiber is the exponential of U(a,b), including empty K. These are natural simplicial isomorphisms, not only vertex bijections.
- Step 10: REPAIRED then PASS against the ground cotensor adjunction: wrote the restriction-map identification and the equation on maps from Delta^n times K explicitly, then wrote iterated representing isomorphisms and the triple-product check for coherence. The constant vertex is b_K under that adjunction.
- Step 11: PASS against exactly the SM7 sentence in the convention node and HTT Remark A.3.1.6: i and p have the required ground classes, and the degreewise equations identify the actual pullback of theta, including its triviality alternatives.
- Step 12: REPAIRED citation then PASS against the full horn/boundary clauses of lem-coef-kan-quillen-right-proper: the written diagonal-and-base pairing proves pullback stability directly; no right-properness or homotopy-fiber theorem is taken from that node.
- New nodes: NONE. B1-B7 and the new-node redundancy tests therefore introduce no obligations; no conclusion has been moved into a restatement node, and no Mathlib leaf is claimed.

For C3/C4, every non-elementary input is an assertion of one of those cited statements; none is taken from a cited proof. Steps 1-10 are universal-property, equality and retract calculations from the stated definitions/axioms; steps 11-12 explicitly cite SM7 and Kan lifting. All 15 step/node citation entries have literal statement-substring quotes, including the repaired horn/boundary quote. I checked the complete dependency closures: 162 nodes under the model convention, one under the colimit definition, and 79 under the Kan theorem; none reaches this item. No new cycle or outside-unit theorem tool is introduced (the cross-unit colimit node is a definition/Mathlib leaf).

Small cases: A initial gives the ground category and mapping objects; the zero object, when present, gives the pointed instance without a further assumption. An empty index gives initial 1_A and terminal A to 1, while a two-object discrete index gives X coproduct_A Y. K empty gives tensor 1_A and cotensor A to 1; K=Delta^0 gives the original object. For source 1_A the fiber is terminal in every simplicial degree, including n=0 and n=1. No claim that Map(A,Y) is Kan is needed, so noncofibrant A is allowed. All pass.

Independent duplicate and attachment searches: searched the whole DAG by undercategory, coslice, simplicial-model terminology and the HTT identifiers, and independently ran blueprint_refs.py searches for undercategory and coslice (both zero blueprint matches) and the ancestor query. Opened the candidate infinity-coslice-colimit, finite-Reedy-localization and enriched-functorial-factorization statements; they concern other structures and do not state this construction. Searched the slopmaster2 project/Comparator and upstream name table by item id and terminology, and searched master as reference only; no finished exact attachment was found.

I ran fresh msearch.py searches with different phrasing: LeanFinder `A model structure on a comma category with fixed domain inherits enriched mapping objects and the Quillen lifting axiom` (eight hits), grep `Under.*[Cc]ofibration|Under.*[Ff]ibration|[Uu]nder.*[Tt]ensor|[Cc]oslice.*[Mm]odel` (24 hits), and Loogle `CategoryTheory.Under, HomotopicalAlgebra.Cofibration` (zero hits). Actual machine search-log records are preserved in searches.jsonl and copied into the item's mathlib_searches with their verdicts. I read Mathlib AlgebraicTopology/ModelCategory/Over.lean:14-26,128-145: ModelCategory.over supplies only the ordinary overcategory structure and Under remains TODO. I also read AlgebraicTopology/SimplicialCategory/Basic.lean:14-30 and SimplicialObject.lean:34-41: generic enrichment of simplicial objects does not supply the undercategory theorem. Thus no exact Mathlib leaf was missed.

Changes: expanded step 10 to remove an implicit repeated calculation and make coherence checkable; enlarged the step-12 Kan quote to cover both facts used; recorded three independent searches; appended this second reading. The first worker's Review by N8 and other sections are preserved, and the item statement, source, dependencies, and remaining eleven steps are unchanged. No new nodes, Lean edits, compilers or live-project writes.

Validation: `python3 /home/ubuntu/weil-launcher-nt/deliver.py N8 lem-coef-simplicial-undercategory-model --no-push` completed successfully with exit code 0 and `OK (not pushed)` at 6631968169, preflight passed. The validation ran through the required server delivery workflow; no forbidden local preflight/check_dag/review_split invocation was made.
