# Worker report

Item: lem-coef-infinity-pointwise-cocartesian-transport. Group: Q74. Stage 1, direct delivery, 2026-10-17.

## Files written

- dag/nodes/sec-six-functors/lem-coef-infinity-pointwise-cocartesian-transport.json: statement, status split; the existing marked lifting proof is retained, and its mapping-fiber and coherence arguments now cite the existing general results they require. Mathlib verdict: no match.
- citations.json: one verbatim statement quotation for every step/node citation.
- report.md and searches.jsonl: review and actual search record. work/ holds the packet-writing scripts only.

No new nodes and no new Mathlib leaves. The current item was copied from the shared repository because this sandbox contained no node or report. Existing proof material, searches, blueprint ancestry, source citations and formalization metadata were retained. No Lean, unit or chapter record was written, and no compiler or Git command was run by the worker.

## Attachments

None. Searches of the designated slopmaster2 WeilConjectures source for the exact blueprint id, pointwise cocartesian transport, cocartesianFibration and IsCocartesianEdge found no matching project declaration. Ordinary pointwise category-theory occurrences do not state this result. The item's upstream audit is none. Its existing side-project Lean metadata records a theorem whose main proof is postponed, not a finished upstream attachment.

## WANTED

WANTED: Lurie, Higher Topos Theory, Definitions 2.4.1.1 and 2.4.2.1, Lemma 2.4.4.1, Propositions 2.4.4.2-3, 3.1.1.6 and 3.1.2.1/3, and Section 3.3.2, for this item; archival copy under literature/. Read online at https://www.math.ias.edu/~lurie/papers/HTT.pdf without downloading a file.

WANTED: Kerodon Tags 0329 (strict/path pullback), 0110 (pasting), 01PF (composition) and 046J (Hom functoriality), for this item; archival copies. Read the online sources. These are Kerodon tags, not Stacks tags. No Stacks statement supplies arbitrary quasicategorical cocartesian exponentiation.

## Findings and corrections

The statement is retained, including the source-vertex quantifier, arbitrary small simplicial K, the exact degreewise fiber, naturality, and compatibility under composition. No statement dispute or coefficient identification arises. The parent blueprint's finite-stage mapping-complex adjunction remains the ancestor route: I read both the historical master file and main-20261015's moved sk-thm-sf-package file. The latter has the same statement and no proof; historical ancestry still points to the master's second proof paragraph. This is a general foundation below that route, not a change to a unit step. The chapter and unit records were read and preserved.

The inherited Step 4's assertion that a homotopy fiber of a path pullback is another homotopy fiber concealed the general pasting calculation. Existing lem-coef-infinity-homotopy-pullback-pasting states exactly the requisite result, including the specified composition of homotopies. New Steps 4-5 apply it to F -> M' -> M over point -> N' -> N. This removes the unsupported identification rather than creating a duplicate fiber lemma. The inherited naturality calculation is separated into Step 6 and now explicitly cites coherent Hom-functoriality.

The inherited Step 7 attempted to glue comparison data over different base faces from contractibility of one fixed long-edge lift space. Contractibility alone does not identify those different spaces. Step 9 now cites existing lem-coef-cocartesian-straightening for coherent restriction over base simplices and keeps the inherited relative marked lifting problems in Step 8 for actual simplicial realizations. The classification theorem is in the same unit, has no dependency path back to this item, and is used only after pointwise exponentiation is proved by marked lifting. No replacement of a chapter or unit step is involved. Step 10 then writes out the mapping compatibility with the actual retained lift triangles.

The redundant statement dependency lem-coef-infinity-pinch-comparison was removed: the statement already specifies its pinched convention via def-cbc-enhanced-diagrams-cones; the pinch equivalence is not an additional notion needed to state it. Its historical search records and side-project Lean metadata are unchanged. proof_deps is exactly the union of step uses. The already accepted off-unit tools remain the functor/cone calculus and composition-spine calculus; their reasons are retained in split_report.tool_uses. The added pasting, straightening and Hom-functoriality results are same-unit tools.

## Not duplicates

No nodes were created. Whole-DAG searches for homotopy pullback pasting, homotopy fibers and coherent transport found the existing pasting, straightening and Hom-functoriality statements, which are reused. Blueprint searches for cocartesian, homotopy fiber and pullback pasting returned no blueprint node with this statement; same_as remains empty. The blueprint ancestor command confirms prop-coef-integral-exceptional-adjoint.

## Mathlib search

The attached searches.jsonl contains fresh actual Q74 invocations: LeanFinder with two semantic phrasings, Loogle for Quasicategory and Cocartesian, a grep of AlgebraicTopology/Quasicategory, and LeanSearch for cocartesian exponentiation. All services answered. LeanFinder and LeanSearch returned IsCocartesian/IsStronglyCocartesian hom-set factorizations and ordinary exponentiable morphisms; Loogle and the quasicategory grep had zero hits. I read Mathlib/CategoryTheory/FiberedCategory/Cocartesian.lean:46-78: its Category instances and unique morphism factorization are not the quasicategory theorem, including its higher coherences. The exact queries and results were appended to the inherited mathlib_searches, without inventing searches or treating unavailability as absence.

## Review by Q74

I read delivery-errors B through E in full and rechecked the item with the cited statements open. No newly introduced statement needs a separate small-case audit. Every reused theorem below is taken from its statement, never its proof. citations.json contains verbatim excerpts, with full statements where a step uses several separated clauses.

Steps 1-3 retain the dual of HTT 3.1.2.1's proof, checked against the online text of 3.1.1.6/Remark 3.1.1.10 and 3.1.2.3. Step 1 uses def-coef-infinity-fibrations for the quantified source-lifting definition, the mapping criterion for equivalence with the stated convention, composition/initiality for degenerate edges, and marked-cocartesian-lifting for precisely the right lifting characterization. Both categories are quasicategories and p is inner as required. Step 2 uses the marked internal Hom definition, the marked-anodyne pushout-product theorem and the degreewise Fun definition. Opposite reverses initial and final edges and preserves the other generators and all closure operations. The second pushout-product factor is a monomorphism, even for empty K. The transposition formulas are written explicitly; marked edges are exactly vertical cocartesian components. Step 3 uses functor/cone calculus for quasicategory closure, the marked lifting theorem to recover the fibration and exact marking, the mapping criterion to recover the original convention, and the fibration definition to lift eta from A. No quasicategory condition on K is imposed.

Step 4 uses functor/cone calculus for the Kan mapping spaces, the cocartesian mapping criterion for its right-hand square, inner-mapping-fiber for both vertical Kan fibrations, the enhanced-diagram definition for the strict fiber, and Kan-pullback-path-comparison for the left-hand square. The test object is in the strict G fiber; hence both left endpoints in the base are G and the chosen vertex is exactly 1_G. I verified the constant initial face and the entire constant base simplex in the pinched fiber. Step 5 uses homotopy-pullback-pasting, whose statement explicitly includes specified homotopies, and composition-spine for the unit path to eta. Its outer rectangle is exactly the desired comparison, so the formula comes from precomposition and its base path. Step 6 uses Hom-bifunctor-functoriality (coherent, not merely pi_0), composition-spine, degreewise constant-path comparison and the pointwise-equivalence clause of functor/cone calculus. Universe enlargement ensures the Hom theorem's local-smallness hypothesis.

Step 7 uses the inner lifting definition to choose a composite over the specified base 2-simplex, then cocartesian-composition-initiality with its required first edge lambda already cocartesian. Both the long-edge lift and direct lift are initial in the same L(A,theta eta). The functor/cone theorem gives the contractible Kan subcategory; composition/initiality explicitly says that forgetting the comparison triangle gives an equivalence in the strict target fiber. Step 8 uses marked-initial-vertex, whose statement supplies the sharp spine inclusion and its full relative parameter clause. Its prerequisite marked lifting property is exactly Step 2's conclusion. I checked T = boundary Delta^r and T' = Delta^r, including r = 0, so prescribed data are retained.

Step 9 uses cocartesian-straightening only for the already established p_K. Its statement gives the fiber values, edge transports, coherent pullback along every map of bases and contractibility of classification choices. This supplies coherence across different base faces, where the inherited proof had a gap. Composition/initiality and functor/cone calculus compare its long-edge lifts to those of Step 7 with triangles retained; Step 8 supplies relative realizations. Step 10 uses composition-spine for the displayed h delta = ((hc)mu)lambda homotopy, the mapping criterion and pasting for the general fiber over theta, and coherent Hom-functoriality for all higher naturality data. All base paths are retained, since the lifted triangles lie over the specified base simplex. Step 11 uses only the degreewise enhanced-diagram definition: the constant-diagram fiber is Fun(K,E_b) and the point/empty-shape identifications are literal, so it is elementary.

For the long-step rule, I read each inherited step above 2000 characters and identified its hidden general inputs before restructuring: homotopy-pullback pasting in old Step 4, coherent restriction across base faces in old Step 7, and coherent Hom functoriality in old Step 8. Existing nodes already state all three, so creating new nodes would be duplication. The revised proof has eleven genuine steps, each under 2000 characters; their general inputs are explicit citations, not just shorter prose hiding the same arguments.

Small cases: K empty makes both Fun objects and the fiber a point; K = Delta^0 gives ordinary transport; identity p gives contractible arrow fibers, not arbitrary discrete hom sets; a product fibration reduces to transport in its constant fiber; p to a point makes cocartesian arrows equivalences and the formula is precomposition by an equivalence; degenerate eta permits the identity lift and gives the identity comparison. No nonempty fiber, existence of diagram limits or colimits, or ordinary category identification is used. I checked the added dependency closures: none reaches this item. There is no new node which could merely restate a clause, and no new definition or hypothesis.

## Unfinished work

None in the requested one-level stage-1 split. The existing cited unsplit inputs remain separate DAG items. Server dry run and direct push are the remaining delivery operations.
