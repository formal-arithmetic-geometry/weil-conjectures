# Q72 stage-1 report: lem-pe-partition-restriction-ind-zariski

## Files written

- dag/nodes/sec-proetale-coefficients/lem-pe-partition-restriction-ind-zariski.json: statement item split into eight complete steps; no exact Mathlib match for the whole statement. Statement and original metadata retained.
- citations.json: verbatim statements for every citation in every proof step, retaining the hypotheses as well as the particular clause used.
- report.md: this report. searches.jsonl is the search command's append-only evidence.

No new nodes, and no new Mathlib leaves. The finite-product comparison is proved directly in steps 5–6 rather than moved to a new node restating the item. No Lean was written or compiled, no repository or launcher file was changed, and no agent was started.

## Attachments

None. Searched WeilConjectures and Sheaf for the exact blueprint id and for ind-Zariski, partition/restriction and clopen/localization terminology. Upstream WContractible constructs a closed graph restriction of a locally constant function ring; PullbackProfinite proves properties of that construction. These do not state all clauses of the present partition diagram and its product-of-neighborhood-indices comparison. The related local StoneanCoverSecondStage theorem is a larger parent theorem, whose docstring includes this argument; it is not an exact upstream attachment for this item.

## WANTED

None. All sources needed for this split were present.

## Corrections and source route

No statement error or hypothesis correction was needed. The imported item had no proof. It already isolates the algebraic part of the parent construction, so the split supplies the actual finite-stage and comparison arguments. No surjectivity of f, w-locality of R, extremal disconnectedness, or relationship between P and the component space of Spec R is used. The hypothesis on S is stronger than the compactness needed for closed images, which causes no change to the statement.

Read GOAL.md, the three blueprint levels in SETUP.md, the chapter and unit records, and the current main-20261015 proof of det-pe-wc-cover-second-stage. This is precisely the unit's second-stage route: clopen neighborhoods, finite products, refinement, filtered colimits. Read Stacks proetale.tex, Tag 097D (lemma-construct-profinite), Tag 097C (lemma-construct), and Tag 096S (lemma-ind-ind-zariski). Read categories.tex, Tag 04AX (section-directed-colimits) and Tag 002W (lemma-directed-commutes), and algebra.tex, Tag 00D6 (lemma-directed-colimit). The blueprint's finite-product parenthetical is expanded on actual representatives and equality witnesses; its proof is agent-written, so proof_origin.by is agent. No prohibited SGA route is involved.

The ind-Zariski conclusion always means the project's finite-principal-product definition. Stacks uses local isomorphisms in its definition; this split does not silently assert an equivalence of definitions. It invokes the existing project's ind-etale-stability node, which explicitly asserts filtered-colimit closure for the project's definition. Its proof and dependencies do not lead back to this item. The off-unit use is declared in split_report.tool_uses as a generic stability tool, just as the parent blueprint cites it; no unit step has been replaced.

## Mathlib and duplicate searches

Before writing the split, searched the whole DAG for ind-Zariski, finite products/filtered colimits, commutative-algebra colimit existence, and element representatives and equality; ran blueprint_refs.py ancestor on the item and blueprint searches for ind-Zariski, finite products, and partition. The item's nearest ancestor is det-pe-wc-cover-second-stage. No other blueprint node states the whole item, so same_as remains empty.

The msearch.py log records actual LeanFinder, LeanSearch, Loogle and Mathlib grep calls, including two semantic phrasings. The first Loogle query used an unqualified unknown name; that diagnostic is retained honestly, and the qualified query was run afterwards. Services were available. The second LeanFinder phrasing found general ring colimit constructions and product comparison maps, not this entire statement. Read Mathlib/Algebra/Category/Ring/FilteredColimits.lean, including colimitCoconeIsColimit and forget_preservesFilteredColimits, and CommAlgCat/Basic.lean:213 for its HasColimits instance. Existing DAG Mathlib leaves already supply the needed algebra-colimit and eventual-equality facts; no leaf was recreated.

## Not duplicates

No new node pairs: zero new nodes. Reused lem-pe-clopen-restriction-canonical-localization for canonical restrictions, lem-weil-pbc-commutative-algebras-colimits-exist for existence, lem-weil-pbc-filtered-colimit-algebras-elementwise for underlying ring colimits and representatives, lem-pc-filtered-colimit-commrings-elementwise for eventual equality, and lem-weil-pbc-ind-etale-stability for closure. The sets/abelian-groups-only node lem-weil-pbc-filtered-colimits-commute-finite-limits is deliberately not used as a theorem about ring colimits: steps 5–6 establish the required ring comparison directly.

## Review by Q72

I checked the split against delivery-errors B–E with the current blueprint proof and the cited node statements open. There are no new statements needing additional sources or searches, no unsplit child carrying a disguised proof, and no renamed clause introduced as a dependency. The proof uses the statements of its dependencies, never their internal proofs. Each non-elementary input has a citation; citations.json copies those statements verbatim. All eight steps are below 2000 characters.

Step 1 proves the closed-image assertion from the definitions: restrict an open cover to the closed part of compact S, and separate a point outside f(A) from its image points by finitely many disjoint neighborhoods. It requires P Hausdorff and f continuous, both stated; it neither assumes f(A) clopen nor assumes f is open. It is marked elementary because the entire finite-subcover argument is written out and cites no black box.

Step 2 uses only the category-colimit definition node's assertion that a nonempty directed poset is filtered. I verified smallness by finite subsets of the power set, antisymmetry using nonempty disjoint parts, and common refinements by nonempty intersections. The empty partition is included when S is empty, so the index is never accidentally empty.

Step 3 uses exactly the canonical-restriction node's maps for closed Z contained in Z-prime and its composition assertion. Step 1 gives closedness, and A-prime contained in A gives f(A-prime) contained in f(A), in the correct direction for R_{f(A)} to R_{f(A-prime)}. Coordinate projection formulas explicitly prove functoriality; no mere definition is cited for a composition theorem.

Step 4 uses the same node's small directed clopen-neighborhood diagram and canonical localization transitions. I checked that coordinate intersections still contain f(A), and that the product of the finitely many neighborhood sets is nonempty, directed and small. The algebra-colimit existence node applies to this small diagram; the category-colimit node supplies exactly the comparison by a compatible cocone. It is not cited for existence. Product addition, multiplication and units make all maps R-algebra maps directly.

Step 5 uses the representative clause of the algebra-colimit node, applied separately to the exact colimits defining R_{f(A)} in the canonical-restriction node. Taking the tuple of the finitely many chosen indices produces a stage of J_Q itself, not an undocumented reindexing. This proves surjectivity without claiming cofinality of a projection or using a sets-only finite-product theorem on rings.

Step 6 uses the algebra-colimit node for representatives in L_Q and to identify each defining algebra colimit with its underlying commutative-ring colimit. Only after that identification is the eventual-equality clause of the ring-colimit node applied. Its indices here are directed neighborhood posets: a common successor is a smaller neighborhood, so the finitely many W_A form a valid tuple. Equality at that tuple gives equality in L_Q by cocone compatibility, precisely what the category-colimit node states. The inverse of a bijective algebra map is checked by applying the injective map to each algebraic equation. For the empty partition the index is a singleton and the source and target stages are zero rings, so the comparison is an identity rather than an appeal to nonempty coordinates.

Step 7 now defines the refinement index functor h explicitly: the child part receives its containing parent's neighborhood, which still contains the child image. Coordinate projections give compatible maps of product stages. The colimit universal property gives d, and both sides of the comparison square have A-prime coordinate iota_(A-prime,U_A) composed with projection to A. The canonical-restriction statement identifies this with r_(A,A-prime) composed with iota_(A,U_A). I checked identity and successive refinements and the empty case. This replaces the earlier choice of unrelated child neighborhoods with a specified functor and an equality on coprojections.

Step 8 uses the precise principal-localization ind-Zariski definition, small-colimit existence, and only the filtered-colimit clause of the generic stability statement. Its hypotheses hold by the partition and product diagram checks above. Added the localization-away definition citation for the edge-case observation R[1/0] is the zero ring, and wrote the fraction-relation check explicitly. Thus the empty finite product causes no failure even if it is represented by a one-factor principal localization instead.

Small cases checked: S empty with P nonempty (no surjectivity is assumed), P empty (forcing S and Spec R empty), zero R, one-part and one-point partitions, f constant, and disjoint nonempty parts with overlapping images f(A). Overlapping images cause no problem because all products are indexed by parts of S, not by distinct images in P. Repeated refinements and identity refinements give the stated same maps; no local-ring, prime-spectrum limit, or component-space theorem is needed in this item. The dependency closure of each generic theorem was checked for a return path to the item; none was found.

## Unfinished work

None in this stage-1 split. The canonical-restriction node is now split and reviewed in the current DAG; it remains an independent dependency whose statement provides the required maps. Delivery validation is performed by the required server-side dry run before pushing.

## Repair of landing return L

The return says the approved side completion had not been promoted into the live DAG. I retained the previous eight-step argument, source references, search results and citation evidence. The required initial dry run exited successfully at 0418df9f9d0 against the delivery tool's current origin/sheaf-dag base. The delivery tool constructs a fresh commit on that base and preserves maintainer-owned fields, rather than reusing the old side completion's commit.

Compared the sandbox item with the current read-only repository: statement, statement dependencies, source, blueprint, chapter and unit still agree; the live item is unsplit and the sandbox supplies its proof, proof dependencies, split report and search additions. Re-read all ten cited definition/theorem statements in the current DAG, including the canonical-restriction node now split and reviewed by L/Q69. All 17 step/node quotes in citations.json remain verbatim in those current statements. In particular that node still gives the small directed neighborhood diagram, the canonical restriction maps and their composition, so its new completion does not require a different proof route. The current stability node still explicitly gives filtered-colimit closure for the definition used here.

This retry contains a mathematical repair as well as the fresh-base delivery: step 7 now supplies the order-preserving index functor h, the product-stage coordinate projections, the induced map of colimits and the explicit coordinate equality proving the refinement square. This removes the earlier underspecified appeal to comparison squares. The report's obsolete description of the canonical-restriction dependency as unsplit has also been corrected. No statement, hypothesis, search question or dependency changed, so the logged searches are reused. Every step remains under 2000 characters. The final dry run and push use only the prescribed delivery tool.

## Current-base retry after returned head 3fee99ec082

The retained sandbox already contains the first repair of return L. I ran the required initial dry run before editing; it exited 0 with preflight passed at 25f6bc528fc. I then compared every item field against the current live read clone. The statement, statement dependencies, source, blueprint ancestry, chapter, unit and creation record agree; only the worker-owned split fields differ. I reconstructed the delivery item from that current live record with the retained proof, citations, searches and split fields, so no obsolete metadata is carried across the fresh-base delivery. The live item is still unsplit, with no released repair note needed.

I reopened all ten current statement/proof dependencies and checked all 17 step/node quotes against their actual statements. In particular the canonical-restriction dependency is now split; its statement still supplies the directed neighborhood system, canonical restriction maps, and their composition exactly as steps 3–7 require. The other current statements retain all quoted assertions. No statement or hypothesis change requires a new Mathlib search, and the existing search log is retained intact. The blueprint Preliminaries and Step 1, Stacks 097C/097D and the filtered-colimit passages were reread. The upstream search again found the closed-graph construction and the sorried larger Stonean-cover theorem, without a declaration stating this whole item.

The retained step 7 already specifies the refinement index functor. This retry additionally spells out its identity and composition on product-stage projections and colimit coprojections, rather than leaving the last coherence assertion implicit. This is a routine calculation with the same two cited statements, not a new lemma or a change of route. All eight steps remain below 2000 characters. The empty-partition case, overlapping images of disjoint parts, neighborhood inclusion directions, smallness and the filtered-colimit stability hypothesis were checked again. The final dry run will check this revised payload before the push; neither an unchanged re-push nor an old side-project commit is used.
