# Q10: lem-cbc-standard-simplex-mapping-contractible

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-standard-simplex-mapping-contractible.json`: statement item split into five steps. Statement and statement dependencies retained. Mathlib has the defining simplicial thickening, but the searches did not find the contractibility and arbitrary-map theorem, so the item is not a Mathlib leaf.
- `citations.json`: one verbatim statement quotation for each of the five step/node citations.
- `searches.jsonl`: seven actual searches made through msearch.py, including two semantic phrasings and two Loogle/grep queries. The item's previous searches are retained; new records reproduce the executed queries and logged results.
- No new DAG nodes; no new Mathlib leaves. `write_split.py` is a sandbox-only construction script, not part of the delivery.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` by the blueprint id and by coherent-nerve, homotopy-coherent, simplicial-thickening, standard-simplex and nerve-contractibility vocabulary. No project declaration states this item. Mathlib's `CategoryTheory.SimplicialThickening.Path` and its simplicial-category structure only supply the model's definition; they do not give every clause of the item.

## WANTED

WANTED: Jacob Lurie, *Higher Topos Theory*, Definition 1.1.5.1 and Remark 1.1.5.2, printed pp. 20-21, for lem-cbc-standard-simplex-mapping-contractible. The IAS PDF was read online in memory, PDF pages 38-40; no archival copy was written.

WANTED: Kerodon Proposition 3.1.7.13 (Tag 00UB) and Construction 3.6.5.1 (Tag 0148), for the cited simplicial-homotopy-equivalence implication. Both pages were read online. These are Kerodon tags, not Stacks tags. No Stacks tag is claimed for the coherent-realization construction.

## Corrections and route

The original statement is true, and no statement correction or STATEMENT-DISPUTED is needed. The item had no proof. The identification with a subset-poset nerve is already an explicit clause of lem-coef-coherent-nerve-comparison. The missing argument is supplied by an explicit simplicial cylinder contraction, not a new node asserting a clause of this item.

I read the current chapter record, unit sk-prop-sf-cbc, the current main-20261015 ancestor proof thm-cbc-finite-level-proetale, and the parent's use in step 1 of lem-cbc-mapping-simplex-universal-equivalence. The item is an auxiliary categorical calculation below that parent's existing route, not the key statement of its unit; no unit realization fields change. The inherited blueprint ancestry and its precise place are retained. Whole-blueprint searches for contractibility, coherent realization and subset nerves found no blueprint node stating this theorem. The off-unit coherent-nerve node is declared as a tool use: only its definition of the mapping sets and union composition is used.

Nothing remains unfinished in this split. The cited nodes remain separate existing items; no Lean was written or compiled.

## Not duplicates

No new nodes. The potentially tempting new statement “a least-element poset has contractible nerve” is not introduced: its chain-level homotopy is a short explicit step. The existing coherent-nerve comparison gives the model, and the existing homotopy-equivalence lemma gives the non-elementary weak-equivalence implication. No duplicate helper or restatement of an item clause is delivered.

## Review by Q10

I checked the item directly against HTT Definition 1.1.5.1 and Remark 1.1.5.2, including the direction of subset inclusion, the endpoint conditions, and union composition. HTT explicitly identifies the mapping realizations with cubes and notes their weak contractibility. Here the contraction is proved directly on chains. I also read Kerodon 00UB and 0148, whose forward implication and realization construction justify the existing homotopy lemma without assuming the mapping nerves are Kan. The local literature lacks archival copies, so proof_origin is correctly marked agent.

For step 1 I opened lem-coef-coherent-nerve-comparison and used its statement's exact defining paragraph, not any argument hidden in its proof. It states the same interval-subset poset and union composition. The least subset is visibly {i,j}; this uses only the endpoint conditions.

For step 2 I opened def-cbc-enhanced-diagrams-cones and checked its ordinary-nerve and standard-simplex definitions. The formula replaces entries before the switch by {i,j}; it produces an increasing chain because {i,j} is contained in every entry. Reindexing by every monotone simplex operator gives exactly the same formula. Thus both faces and degeneracies commute, and the two endpoint maps are exactly the constant minimum and the identity. This is the actual contraction, with no uncited general nerve-contraction theorem.

For step 3 I opened lem-cbc-simplicial-homotopy-equivalence-weak and checked every hypothesis against p:X→Delta^0 and s:Delta^0→X. Step 2 gives sp homotopic to id_X, while ps is literally the point identity, with a constant second homotopy. Its statement explicitly allows non-Kan simplicial sets and either endpoint order. This proves precisely the terminal map is a weak equivalence.

For step 4 I used the definition's component/group criterion. The equality p_Y f=p_X gives bijectivity on components by cancellation. At each x the map on homotopy groups of p_Y is based at f(x); the displayed inverse-composite formula is therefore well-typed and proves the isomorphisms for all n≥1. Functoriality here is just associativity of postcomposition in the given definition of the induced maps. There is no uncited model-category two-out-of-three assertion.

For step 5 I checked the quoted coherent-realization statement's composition clause again. The map is specifically S↦S∪{r−1,r}, which stays in the target poset and preserves inclusion. Step 4 applies to this map itself, rather than to a chosen comparison map. This supplies the final requested composition clause.

Edge cases checked: r=0 and i=j give a one-object poset; adjacent endpoints give a point; r=2,i=0,j=2 gives the two-object chain {0,2}⊂{0,1,2}; i=r−1 makes the composition source a point; r=1 gives the point-to-point composition. No empty mapping set occurs under i≤j, so none is incorrectly called contractible. Maps between different simplex dimensions are covered in step 4.

Against delivery-errors B–E: no new-node shape, hidden hypotheses, or duplicate problem arises; every cited node's statement was opened and the exact usable clause copied into citations.json; every non-elementary implication is the cited homotopy lemma; the contraction and composition formulas are written out; there is no circular dependency (the closures of the three used nodes do not contain this item). All five steps are shorter than 2000 characters and hide no comparison lemma. The statement, ancestry and parent use agree. No SGA source or replacement route is used.
