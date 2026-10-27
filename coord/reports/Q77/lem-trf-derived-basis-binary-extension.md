## Worker report

Q77 split lem-trf-derived-basis-binary-extension without changing its statement or statement dependencies. Written: dag/nodes/sec-trace-formula/lem-trf-derived-basis-binary-extension.json (statement, split, no Mathlib match), citations.json (one verbatim statement quotation per cited node per step), and this report. The local write_split.py is a sandbox-only writing aid, not delivery material.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. Both non-elementary inputs already exist. No other node, unit, chapter, Lean source, repository file or launcher file was edited.

## Attachments

None. Searching lean/WeilConjectures for the exact blueprint tag, BBD, derived gluing, basis descent and negative self extensions found no declaration stating all clauses of this item. AlgebraicGeometry.derived_open_gluing_objects (AlgebraicGeometry/DerivedOpenGluingObjects.lean:108) is a real object-gluing theorem but provides neither canonical overlap comparisons nor the original-family maps; it belongs to the existing lem-sc-derived-open-gluing-objects and is used through that node. Its source file contains no sorry, but no closure claim is needed for this split.

## Literature and searches

WANTED: none. I read literature/stacks-project/cohomology.tex, labels lemma-glue (08DG), lemma-vanishing-and-glueing (0D66), lemma-uniqueness (0D68), remark-uniqueness (0D69), lemma-solution-in-finite-case (0D6A), and theorem-glueing-bbd-general (0D6C). The proof is the 0D69/0D6A binary construction with already supplied solutions on the two unions, using 08DG. I checked tags against stacks-project/tags/tags. No SGA source is used.

I read the current blueprint latest/sec-trace-formula/sk-i-curve-zero statement, proof and section (under literature/blueprint/latest/blueprint), as well as the chapter and unit records. This is the existing auxiliary derived-descent branch beneath lem-trf-local-term-locality, not a change of the chapter or unit route. The blueprint ancestor search returned lem-trf-local-term-locality. Whole-blueprint searches for 'derived gluing', 'negative self', and 'two open' found no blueprint node stating the item; the last search found only unrelated Nagata and exterior-product nodes. Whole-DAG searches for 0D69, 0D6A, 0D6C, 0D68 and for derived gluing/local Hom identified the existing local-Hom node and the existing 08DG object-gluing node, which I opened and read.

The item's previous Mathlib searches were retained. I also ran the mandated msearch.py leanfinder, loogle, grep and leansearch commands, then a second leanfinder phrasing about compatible morphisms and negative Ext. All five completed successfully; their exact queries, returned declaration names and digests are in searches.jsonl and in mathlib_searches. The hits give ordinary sheaf/topological gluing or abstract derived-category and Ext facts, not this assertion. In particular the ordinary sheaf gluing results require an actual sheaf; proving derived Hom is such a sheaf is exactly the existing local-Hom input. DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE requires degree bounds absent here. I read the corresponding Mathlib UniqueGluing, DerivedCategory.Basic and Fractions source sections. No service failure was represented as absence.

## Faults and corrections

The imported item had no proof. Its statement is sound and is preserved verbatim. The family is only intersection-refining, not necessarily a basis for the whole topology; I consistently use the existing lem-trf-derived-basis-local-hom-glue, whose statement explicitly treats this weaker family. It is never silently replaced by an ordinary topological basis.

The source's two-open proof leaves the final solution equations to the reader. Steps 5-7 supply those equations, including structure maps on U contained in neither piece. Instead of assuming restriction detects isomorphisms, steps 2 and 6 glue the inverse maps and compare composites with identities using the same cited Hom bijection. Thus no uncited locality theorem is needed.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. Reused lem-trf-derived-basis-local-hom-glue for all unique morphism gluing and lem-sc-derived-open-gluing-objects for 08DG object existence; no clause of this item was repackaged as a new node.

## Tool use

lem-sc-derived-open-gluing-objects, from sk-thm-picard-duality, is the generic 08DG two-open object-gluing theorem used as a black box on the open scheme O. It is exactly the construction the source 0D6A calls, and no separate node of this unit supplies it. This is declared in split_report.tool_uses for the maintainer's route review; I did not set the maintainer-owned top-level tool_uses. The local-Hom node is already in this item's own unit.

## Review by Q77

I checked the item against 0D69 and the n=2 argument of 0D6A, reading 0D68 and 08DG for their hypotheses. There are no new statements to review. The supplied solutions, their inclusion equations, and negative self-Hom on every member of the original family are precisely the data the proof uses; neither quasi-compactness, quasi-separatedness, boundedness nor affineness is introduced.

Step 1 is the pointwise refinement argument for finite intersections of unions. It proves the cover property needed later, without claiming that all opens are unions of the given family. It uses no external theorem. All opens involved are open subschemes by the statement's scheme convention.

Step 2 cites the statement of lem-trf-derived-basis-local-hom-glue, which provides negative Hom vanishing and a bijection for inclusion-compatible morphism families on an intersection-refining cover. On W both solution restrictions are global objects. On each V in its indexing family both identify with K_V, so all four ordered-pair negative-Hom hypotheses follow by conjugation with the specified isomorphisms. The displayed cancellation checks inclusion compatibility. The reverse family gives an inverse, and the two endomorphism applications of injectivity verify both identities. This uses the cited statement, not anything hidden in its proof.

Step 3 uses the same bijection's injectivity for F_1,F_3 on the triple intersection. The explicit local composite s_3,V^{-1}s_2,V s_2,V^{-1}s_1,V equals s_3,V^{-1}s_1,V; its negative-Hom hypotheses hold on the restricted original family. Hence the cocycle follows without a new lemma.

Step 4 cites the exact statement of lem-sc-derived-open-gluing-objects. It gives F and both isomorphisms with the required transition for any scheme covered by two opens; no morphism-lifting or uniqueness clause is taken from it. The ambient scheme is the open subscheme O and its cover is O_1,O_2. Its canonical iterated-restriction comparisons are also the ones used by this proof. Thus no extra boundedness or cover hypothesis is missing.

Step 5 is elementary after steps 2 and 4: the family C_U covers by refinement of U with a member lying in one piece; a smaller member remains in the same piece. The overlap comparison makes tau independent of the piece. Restricting the solution equation and multiplying by (rho_V^U)^{-1} proves the displayed b-family equations. These are actual equations, not an appeal to unspecified transport or compatibility.

Step 6 applies the local-Hom statement on the scheme U with family C_U. This is legitimate even when U crosses both pieces, since the statement only requires an intersection-refining covering family. The maps tau_V and rho_V^U identify both restricted objects with the same K_V. Its bijection glues b_V and the inverses; injectivity for the endomorphism pairs proves that the resulting map is invertible. I read its empty-cover clause as well, so no unproved nonemptiness assumption is concealed.

Step 7 uses that same injectivity twice. First it compares with the already supplied map on a piece. Second, for T contained in U, C_T is a subfamily of C_U; the displayed equation after composing with rho_V^T gives equality on every V in C_T, and cancellation plus the bijection gives the inclusion equation on T. The same pair identifications check the hypotheses for both applications. This proves the clauses the source leaves to its reader, for every member of B_O, not just members in a piece.

Small cases checked: the empty scheme with empty family (the cited Hom statement expressly includes it); one or both pieces empty; disjoint pieces; repeated pieces; a member U crossing O_1 and O_2; U contained in one piece but V contained in both; and an unbounded complex with negative self-Hom zero. Each uses the same construction and none requires a finite subcover of a member. No new source error or statement dispute arose. The source contains harmless variable-name slips in the last comparison of 0D6A, which I replaced by the typed map F|_U to K_U in this proof without changing any assertion.

I checked delivery-errors B-E with the files open: no statement-only-node violation because no new nodes; actual theorem statements support each citation (citations.json quotes them verbatim); all non-elementary steps cite the local-Hom or object-gluing theorem; no elementary step imports a hidden cohomological assertion; no duplicate or self-restatement; no statement change, omitted hypothesis, or wrong open; and no reliance on a dependency's proof. Every step has fewer than 2000 characters. I checked both dependency branches against the item for a potential cycle; final authoritative cycle and route checks are delegated to the required server dry run. This is Q77's direct-delivery self-review; there is no second worker.

## Unfinished work

None in the stage-1 split. The two existing nodes remain the downstream proof inputs. Required server dry run and delivery are recorded by the delivery tool.
