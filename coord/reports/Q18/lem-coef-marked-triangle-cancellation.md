# Q18 stage-1 report: lem-coef-marked-triangle-cancellation

## Files written

- `dag/nodes/sec-six-functors/lem-coef-marked-triangle-cancellation.json`: existing statement, now split in six proof steps; no Mathlib match.
- `citations.json`: eight entries, one for each step/node use, checked to be literal substrings of the cited statements.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0. The sandbox also contains the item-specific preparation script `write_split.py`; it is not a DAG delivery file.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` source for the item id, marked simplicial sets, marked anodyne maps and triangle cancellation; there is no project declaration giving this item. A second search in the read-only upstream master source found no item-id or marked-anodyne declaration. No Lean file was written and no compiler was run.

## Wanted literature

WANTED: Jacob Lurie, Higher Topos Theory, Definition 3.1.1.1, Remark 3.1.1.3, Proposition 3.1.1.6, Corollary 3.1.1.7, Proposition 2.4.1.7 and Proposition A.1.2.5, for lem-coef-marked-triangle-cancellation. I read the IAS PDF online at https://www.math.ias.edu/~lurie/papers/HTT.pdf; there is no archived HTT under the named literature directory. I did not download it. The proof_origin is consequently agent, with the exact online source and places recorded. No Stacks tag states the marked-simplicial result; assigning a Stacks tag would misidentify the source. No SGA source is used.

## Findings and corrections

The imported statement is correct and is unchanged. The marked horn in HTT Corollary 3.1.1.7 is Lambda^2_2, whose edges are [0,2] and [1,2]; thus its asserted remaining marking is exactly [0,1]. The item previously had no proof. Its source, ancestry, chapter, unit and all maintainer fields were preserved. There is no blueprint_update on this item or its nearest blueprint ancestor.

HTT invokes the relative marked lifting characterization, not merely the point model structure. Citing the existing lem-coef-marked-relative-cartesian-model or lem-coef-marked-point-cartesian-model would lead through the current item. I expanded only the forward marked-lifting argument instead, using the existing cocartesian composition lemma on opposite simplicial sets. This keeps all mathematics in the item's steps and requires no restatement node for either cancellation or the relative model structure.

The searches `blueprint_refs.py search 'marked triangle'`, `search 'marked anodyne'`, `search 'cocartesian composition'` and `search 'marking'` found no blueprint node stating this item. The broader Cartesian search and the DAG statement scans located the reusable cocartesian-composition node and the relative model nodes; their statements were opened and distinguished. The ancestor command returned prop-coef-integral-exceptional-adjoint, matching the existing ancestry. The lemma is a technical input under that ancestor's integral adjunction/limit calculation; the fixed chapter and biduality unit route are preserved. No coefficient category or base-change morphism is altered or identified.

I ran fresh logged LeanFinder, Loogle, grep and LeanSearch searches with msearch.py and a second LeanFinder phrasing. The hits are unmarked horn inclusion/desc declarations or abstract model-category weak factorization instances, not the marked cancellation inclusion. I read HornColimits.lean and ModelCategory/Basic.lean in the read-only Mathlib checkout. The grep for `def ι₀₂|def ι₁₂|instIsWeakFactorizationSystemTrivialCofibrationsFibrations` in AlgebraicTopology returned zero: the horn inclusions are abbreviations and the factorization instances are anonymous, so I did not interpret that query as evidence that those general declarations do not exist. Its actual result is recorded. All six fresh query texts and their actual outcomes are appended to the existing search records; none is invented and no service was unavailable.

## Not duplicates

No new node was created. Existing lem-coef-infinity-cocartesian-composition-initiality supplies cancellation after reversing vertex order. The point and relative model-structure nodes do not state the independent forward relative lifting assertion needed here and cannot be cited because of their dependency path back to this item. The core-Kan and converse outer-horn facts are reused from their existing cbc nodes, rather than recreated.

## Review by Q18

I read the chapter and unit records, the item's statement and ancestry, and HTT Definition 3.1.1.1, Remark 3.1.1.3, Proposition 3.1.1.6 and its proof, Corollary 3.1.1.7, and Proposition 2.4.1.7 with its proof online. I compared every use with the complete statement of the cited DAG node. The original statement has the same four generators, same final-edge marking, and same weak-saturation closure as HTT. In particular it is not the opposite marked-coanodyne convention.

Step 1 is the explicit countable-subcomplex argument, not a citation to a hidden small-generation theorem. A finite horn lies at a finite stage of the countable construction, so its chosen filler appears at the next stage. Each marking attachment keeps the underlying K and adds exactly the marked edges of the chosen subcomplex. Empty K gives the identity, and degenerate edges impose no additional attachments. This proves the reduction from all small Kan complexes to a set of countable representatives and shows why J-injectivity suffices for all four generators. There is no cited node in this elementary construction.

Step 2 uses the actual factorization assertion of lem-coef-small-object-cell-factorization. I verified all its hypotheses: Hom sets are small, marked colimits have the stated edge-image formula, J is a small set with countable domains, J-cell successor maps are monomorphisms, and regular aleph_1 bounds the countably many simplex and marking appearances. Equality of maps is likewise detected at a common stage. Coproduct attachments are serialized, placing j in the item's class W. The use of def-coef-infinity-fibrations is exactly its inner-horn and final-outer-horn definition. The n=1 generator is treated separately: it gives a marked lift with the prescribed target. The base here is the nerve of the order [2], hence is a quasicategory; filling its inner horn and then applying p's lift proves that Z is a quasicategory. The step does not assume an ambient model structure.

Step 3 uses the conditional cancellation clause, not the initial-lift clause, of lem-coef-infinity-cocartesian-composition-initiality. In the opposite triangle the ordered vertices are (2,1,0); the first edge is g^op, the second is f^op, and the long edge is h^op. Thus exactly the hypotheses in that node are present. The horn definition in def-coef-infinity-fibrations makes reversal turn cartesian into cocartesian and preserves the inner-fibration/quasicategory hypotheses. Both g and h are marked by j, so their cartesianness comes from Step 2. This proves cartesianness of f without any assertion that a cartesian edge has already been marked.

Step 4 chooses the marked f' using the n=1 generator, with target exactly sigma(1). The horn for the comparison triangle has final edge f', so it is a legitimate type-(ii) lifting problem even though f need not yet be marked. Its base is s_0[0,1], with vertex list (0,0,1), and the comparison a therefore lies over the degenerate edge at 0. I again checked the exact cancellation hypothesis in the cocartesian node on opposites. The fiber F is a quasicategory by the constant-base lifting argument. The definition node then supplies final-outer-horn fillers for a within F; the *converse* clause of lem-cbc-equivalence-outer-horn-filling makes a an equivalence there. No implication about the core was taken from that criterion node.

Step 5 takes the core-is-Kan assertion from lem-cbc-enhanced-functor-cone-calculus, which explicitly states it for any quasicategory. It applies to F, already shown to be one. The generator-(iv) lifting square has bottom the constant marked map to 0 in the fully marked B. Since its left map is the underlying identity, the filler really is the inclusion with enlarged marking; this forces a to be marked. Generator (iii) now applies to the consecutive edges (a,f') in the comparison triangle and marks its long edge f. I checked this does not confuse the consecutive-edge composition generator with the target cancellation assertion.

Step 6 is the explicit retract, not a claim that a model-category trivial cofibration equals W. Once f is marked, the underlying j defines s on B with the same underlying two-simplex map, si=j and ps=1_B. The two arrow morphisms (1_A,s) and (1_A,p) have identity composite, so retract closure gives the target. Degenerate or coinciding image edges do not change the argument, including the case that f or a is already degenerate or marked; all generators allow such simplicial maps.

These checks address delivery-errors B through E: there are no new-node clauses, elementary facts promoted to nodes, unverifiable source tags, or duplicate nodes. Every non-elementary fact is a node citation, and every quote in citations.json is verbatim from its statement. The countable construction, fiber restrictions, opposite variance, horn dimension-one case, and arrow retract are written out rather than hidden behind 'transport' or 'standard'. I checked by traversing statement and proof dependencies that none of the five cited nodes reaches this item, so no new cycle is introduced. The two off-unit cbc uses (converse outer-horn criterion and core-Kan property) are declared in split_report.tool_uses; they are generic simplicial tools unavailable in this unit's own statements. No statement dispute or new hypothesis was needed.

## Unfinished work

No mathematical part of this item is left to a new node. Existing cited nodes retain their own independent states. This delivery is stage 1 only; it supplies no Lean implementation. A fresh second reader is still required by the dispatch protocol and will deliver after review. The required no-push dry run is run after writing this report; its acceptance leaves this sandbox for that reader.

## Second reading by Q18

I reread HTT Definition 3.1.1.1, Remark 3.1.1.3, Proposition 3.1.1.6, Corollary 3.1.1.7, Proposition 2.4.1.7, and the cited DAG statements. The item's four generator families, the final-edge marking in family (ii), the pushout/transfinite/retract closure, and the marked edges [0,2] and [1,2] agree hypothesis by hypothesis with Corollary 3.1.1.7; no statement change was needed. There are no new nodes to review (and therefore no B1--B7 exceptions).

Step 1: checked the countable Kan-subcomplex construction against HTT Remark 3.1.1.3 and the definition of W; the finite-horn and countable-stage argument is written explicitly and is elementary.

Step 2: checked every hypothesis of [lem-coef-small-object-cell-factorization] (small Hom sets, countable domains, colimit smallness, and regular aleph_1), and checked [def-coef-infinity-fibrations] for inner lifting, the n=1 marked lift, and cartesian marked-edge horns; the factorization and the quasicategory argument are correctly stated.

Step 3: checked the ordered vertices after passage to opposites and the exact conditional clause of [lem-coef-infinity-cocartesian-composition-initiality]; the first and long edges are the required cocartesian pair, so cancellation gives cartesianness of f.

Step 4: checked the n=1 lift target, the type-(ii) n=2 horn with edges [0,2] and [1,2], the constant base edge, the fiber quasicategory, and both hypotheses of [lem-cbc-equivalence-outer-horn-filling]; the conclusion that a is an equivalence in the fiber follows.

Step 5: checked the core-Kan assertion of [lem-cbc-enhanced-functor-cone-calculus], the marked lifting square for generator (iv), and the consecutive-edge source of generator (iii); the underlying maps are identities, so the marking conclusions are valid.

Step 6: checked the marked section, the equations si=j and ps=1, and the arrow-category retract; this is elementary.

I tested the small cases relevant to this simplicial statement: the empty Kan complex makes generator (iv) an identity, a point has only its degenerate edge, n=1 is used exactly for the marked lift and has the required final edge, and n=0 is correctly absent from family (ii). The identity case and already-marked f case also reduce to the displayed retract. These checks expose no zero-object or empty-base exception because the proof is entirely in marked simplicial sets over the fully marked 2-simplex.

I searched the existing DAG for the item, marked-anodyne cancellation, horn cancellation, and the cited cocartesian/core facts. The cancellation item has no existing duplicate or Mathlib declaration; the two model-structure nodes that would create a dependency path through this item were not cited. No proof or statement correction was needed. Changes: I added this second-reading section and three independently run Mathlib searches (LeanFinder, Loogle, grep), with their actual log entries and verdicts; citations.json remains verbatim and consistent with the eight non-elementary uses.

The fresh LeanFinder query used weak saturation and horn inclusions rather than the first worker's missing-edge phrasing. Its eight hits are unmarked Quillen horns, quasicategory horn fillers and horn colimit declarations; Loogle (SSet, Cartesian) and grep (MarkedSSet/MarkedSimplicial/marked cartesian) returned zero. Read the Quillen horn declaration in CategoryWithFibrations.lean:49 and the inner-horn filler clauses; none states this marked map. Independent read-only scans of both source trees found no marked-anodyne or item-id declaration. A direct check of all eight citation quotes returned true, and a dependency traversal from each of the five cited nodes found no path to the item.
