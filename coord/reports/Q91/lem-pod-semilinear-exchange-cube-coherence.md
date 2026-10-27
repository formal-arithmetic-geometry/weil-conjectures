## Worker report

1. Files written: dag/nodes/sec-poincare-duality/lem-pod-semilinear-exchange-cube-coherence.json — statement, split into eight steps, no Mathlib match. citations.json records every step/node citation. No new nodes or Mathlib leaves.
2. Attachments: none. Searched lean/WeilConjectures for the exact blueprint id, semilinear exchanges, and Frobenius cubes. No project declaration states the item. The general Mathlib mate and module-pushforward declarations do not identify these specified constructible/coefficient/compactification comparisons.
3. WANTED: none. The argument follows the latest blueprint's lem-fix-weil-operations proof, with the relabeling and Weil-morphism equations supplied explicitly by Q91. No SGA source is used.
4. The imported node had no proof. Its statement and all its existing metadata are retained. In particular the structural schemes need not be separated over k. The inherited unit is sk-lem-finite whereas its explicit blueprint ancestor is prop-weil-operations in sk-thm-frobenius; this work follows the recorded ancestor and uses generic tool interfaces, without changing either unit record. No statement dispute or route replacement was needed.
5. Nothing mathematical remains unfinished in this one-level split. Existing dependency proofs are independent work items.

## Sources and searches

Read AGENTS.md, SETUP.md including all three blueprint levels, GOAL.md, STATE.md, roles/worker.md, stages/1-dag.md, coord/brief-stage1.md, and delivery-errors.md B–E (including the merged copy). Read the chapter and inherited unit records and the latest sk-thm-frobenius unit. Read literature/blueprint/latest/blueprint/sec-poincare-duality/sk-thm-frobenius/prop-weil-operations.proof.md, sec-six-functors/sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md, and sec-six-functors-basics/sk-prop-sf-cbc/fix-lem-exchanges.md and .proof.md. The actual argument uses the current DAG statements, whose coefficient restrictions are more precise than the sketch.

Searched the entire DAG for relabeling/structural twisting and existing cube and pasting interfaces, and ran blueprint_refs ancestor plus searches for exchange, semilinear, Frobenius and pasting. The existing fix-lem-exchanges supplies all non-elementary coherence laws. Therefore no elementary relabeling lemma or clause-restating child was created. The required logged Mathlib commands included all four services, with a second semantic phrasing. All returned successfully; their actual query texts and hit summaries are in mathlib_searches and searches.jsonl. Read the general mate/pushforward infrastructure; it does not state this item.

## Not duplicates

No new nodes. In particular fix-lem-exchanges is cited instead of duplicating its cube naturality, pasting or refinement clauses. lem-pur-weil-semilinear-exchange-reindexing requires separated structural schemes, unlike this item, and was not used to hide that missing hypothesis. lem-pod-constructible-mate-coherence depends on this item and was not cited, avoiding a cycle.

## Review by Q91

I read the current statements of every dependency used, rather than taking facts from their proofs. The eight proof steps use these statements as follows.

Step 1 uses lem-weil-frobenius-square-cartesian for actual invertible Cartesian Frobenius faces and the commutation with each descended arrow. def-weil-finite-type-morphism supplies the finite affine-generator criterion: twisting the scalar inclusion by a field automorphism leaves its image and hence the generators unchanged. def-weil-proper-morphism defines separatedness by the underlying diagonal. These justify relabeling without imposing separated structural maps. The linearity equation is written out with the new structural maps.

Step 2 uses def-weil-pbc-proetale-site to check that neither objects nor coverings depend on the auxiliary k-structure. def-weil-derived-pullback-tensor-hom and def-weil-derived-direct-image give the actual operation constructions. def-exchange-projection gives the precise unit/comparison/counit composite and higher coefficient data. The argument uses identical sites, module functors, resolutions and strict diagrams, so it does not assert that maps in a derived category are detected by individual reductions. fix-lem-exchanges is applied only after its k-linearity hypothesis has been supplied.

Step 3 takes naturality in square data, with pre/post-whiskering, from fix-lem-exchanges clause (1), or its horizontal-pasting clause (2). I expanded the two iterated Frobenius comparisons and wrote the entire resulting cube equation. Its source is P_(Y') V A_f K and its target A_(f') U P_X K. This proves the required exchange equation without claiming ordinary base change is invertible for arbitrary v.

Step 4 uses Cartesian Frobenius faces from lem-weil-frobenius-square-cartesian and the vertical-pasting equation, including the stipulated direct-image composition isomorphisms, from fix-lem-exchanges clause (2). Both sides have source P_Z A_h A_f K and target A_(hf) P_X K. The ordering A_h(c_f) c_h is checked explicitly.

Step 5 uses the actual chosen/base-changed compactification formula in def-exchange-projection and the relative definition in def-weil-compactifications-refinements. It constructs the new structure on the base-changed compactification through p' and a_Y g_Y. This avoids the false assumption that an arbitrary chosen compactification descends to k_0. The inverse to its base-change projection is obtained from the inverse base isomorphism. Properness is relative to Y, not to k.

Step 6 uses fix-lem-exchanges clause (4), which really states refinement compatibility AND composition compatibility on its coefficient/witnessed domain. Applying it specifically to the Frobenius square yields the displayed r-equation. Inserting comparisons and cancelling inverse pairs explains the intertwining, rather than merely saying that maps transport.

Step 7 uses only naturality of the transformations already constructed and the exact morphism equation of def-weil-weil-sheaf-complex. I wrote the calculation at theta_K; it applies to arbitrary field-category Weil structures and needs no Frobenius-stable lattice.

Step 8 uses the coefficient clauses of fix-lem-exchanges and the specified rational/common-stage map formulas and tower cocycles in def-exchange-projection. Equality is passed by functoriality and linearity, not by attempting to reduce rational objects. Common-stage source/target conjugations cancel at intermediate objects. The final restriction retains all constructibility, finite-Tor, lattice and witnessed-origin assumptions of those statements.

I tested identity maps (the equations reduce to naturality/identity pasting), empty schemes, a point with an arbitrary invertible Frobenius matrix, and finite-type non-separated schemes with separated identity arrows (for example the affine line with doubled origin). The last case checks why structural separatedness must not enter; the proof uses none. For compactifications no chosen Frobenius lift on the compactification is presumed. No proof step exceeds 2000 characters; none hides a new lemma with independent hypotheses. All 17 step/node references have literal statement quotations in citations.json. B–E checks found no new-node, duplication, coefficient-type, circularity, or source-substitution defect. No Lean was written and no compiler/build was run.
