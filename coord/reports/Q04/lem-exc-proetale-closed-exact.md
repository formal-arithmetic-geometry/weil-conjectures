# Worker report: lem-exc-proetale-closed-exact

## Files written

- `dag/nodes/sec-smooth-purity/lem-exc-proetale-closed-exact.json`: existing statement, now split into seven steps; not a Mathlib leaf. The statement is unchanged.
- `citations.json`: 30 step/node entries with verbatim statement quotes.
- `report.md`: this report. `searches.jsonl` is the search command's own log; the two Python scripts in this sandbox only prepared this delivery.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: this auxiliary node is not the statement of its unit.

## Attachments

No closed attachment is claimed. The candidate is
`AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isCompl`,
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures/SixFunctors/ProEtale/UpperLowerStar/ClosedImmersion.lean:178`.
Its own proof has no `sorry`, but it calls `epi_lowerStar_map_of_isCompl`, which uses
`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_counit` in the same file at line 66; the latter's body is `sorry` at line 68. Traversing the committed `local/sorry_map_slopmaster2_7d675a26.jsonl.gz` from the candidate visits 178 declarations and finds exactly this declaration with a direct sorry. The missing proof already has the node `lem-exc-proetale-closed-fully-faithful`; it needs no new node. The source candidate states finite-colimit preservation for arbitrary rings, with finite-limit preservation supplied by the right-adjoint instances. This matches the intended exactness, but is not finished under SETUP's transitive proof-closure rule. The imported `lean_audit` says `none`, so this is also a metadata discrepancy for maintenance. No maintainer-owned field has been changed.

Searches of the specified project source by blueprint id and by pro-etale closed immersion/exactness found no alternative closed proof. The exact upstream master was read only as reference material, never as proof completion evidence.

## WANTED

None. All sources used are available locally.

## What was wrong and what changed

The imported proof omitted the theorem turning an epimorphism into local lifts and back, and omitted the justification that this theorem applies to module sheaves rather than only abelian sheaves. It also left affine/basis locality, the slice-site interpretation of a covering over the closed fibre, and the quasi-compact-complement base change implicit. These are now explicit uses of existing nodes. Kernel preservation is computed on sections, so no uncited general right-adjoint theorem is needed. The last step explains exactness rather than only asserting it after epimorphism preservation.

The imported source points to the whole Stacks section 09A9. I read the exact lemma 09BM, `proetale.tex`, label `lemma-closed-immersion-complement-retrocompact-exact`, and the closed-lift lemma 09BK, label `lemma-closed-immersion-affines`. The proof of 09BM itself proceeds via thickening and a finite-morphism result; that is not silently substituted for the blueprint's covering-lift argument. The retained argument is marked `proof_origin.by = agent`. Its step sources identify the current `main-20261015` blueprint proof, while the item's imported source and other maintainer fields remain untouched.

The unit JSON still records the older finite-type formulation; I also read the current blueprint unit, which has the unbounded ordinary-etale formulation for schemes admitting compactification. This item is the auxiliary pro-etale exactness input, unchanged in both snapshots, and its covering-lift proof does not alter either unit statement or its exceptional-adjunction argument. The unit's old reference to SGA was not used. No SGA source is cited by this delivery.

## Reuse, searches and not duplicates

No new node was needed. I searched the whole DAG and blueprint by the item id, closed direct image, exactness on all pro-etale sheaves, epimorphism/local surjectivity, finite affine ind-etale covers, quasi-compact base change, and their relevant tags. `tools/blueprint_refs.py ancestor` identifies this blueprint node itself as the ancestor. Whole-blueprint search found no second blueprint node giving this exact general statement, so `blueprint.same_as = []`. Some other nodes assert stronger packages or versions with Noetherian hypotheses; none is used to move the item's conclusion into a substitute lemma.

The reused general-site local-surjectivity theorem is `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`, not the similarly named etale-only lemma. The reused base-change theorem is `lem-pc-quasi-compact-base-change`, which allows arbitrary base change; the argument does not require the base or complement to be globally quasi-compact. Existing `lem-exc-closed-cover-extension` supplies both the covering and the specified closed reductions. Existing `lem-weil-pbc-ind-etale-basis` supplies the finite refinement, not just an abstract equivalence of sheaf categories.

All Mathlib searches were made with the required `msearch.py Q04 lem-exc-proetale-closed-exact` command and recorded from its actual outputs. LeanFinder was tried with two phrasings; the first returned etale algebra and unrelated exactness declarations, the second condensed local-surjectivity declarations. LeanSearch returned closed-immersion scheme properties. Loogle tried the right-adjoint/finite-limit pattern and then `"pushforward", "exact"`; both returned zero hits. Grep found the pro-etale-site definition and unrelated category-theory pushforward mentions, not the closed pushforward theorem. I read `Mathlib/AlgebraicGeometry/Sites/Proetale.lean` and the source candidate. General sheaf epimorphism tools do not extend closed-fibre coverings; they do not make the item a one-line Mathlib specialization. No unavailable service was recorded as absence. No duplicate pairs need reporting because there are no new nodes.

## Review by Q04

I read both current blueprint files for the item, the current unit and the imported chapter/unit records, and Stacks `proetale.tex` 09BK/09BL/09BM. I also read the kernel/cokernel paragraphs and lemma 03DA (`lemma-abelian`) and 03CN(5) (`lemma-abelian-abelian`) in `sites-modules.tex`. The unchanged hypothesis is exactly a closed immersion with retrocompact complementary open, meaning that its inclusion is quasi-compact. No Noetherian, finite-presentation, constructibility, boundedness, or finiteness-on-module-values hypothesis is introduced.

Step 1 uses the actual section formula in `def-weil-pbc-proetale-operations` and sectionwise kernels in `def-weil-sheaf-of-modules-category`. The displayed kernel equality is a calculation at every site object, with the same coefficient action and restrictions, so it proves the required elementary assertion without using the proof of either cited node.

Step 2 uses `lem-weil-pbc-module-sheaves-colimits-forgetful` specifically for preservation of cokernels and faithfulness/exactness, and `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective` specifically for the two directions of the covering-and-sections criterion on an arbitrary site. Its quote contains that whole criterion. Reflection of zero is written out, since a module sheaf with underlying zero sheaf has only the zero section. `def-weil-pbc-proetale-site` supplies the small-skeleton universe convention. Thus an etale-only epi theorem is not being applied to the pro-etale site.

Step 3 uses the covering and finite-basis clauses of `lem-weil-pbc-ind-etale-basis`, the underived localization clause of `lem-exc-closed-localization`, base-change stability of closed immersions in `lem-weil-pbc-proper-fp-permanence`, and the affine characterization in `def-weil-closed-immersion`. The generic weak-etale stability statement ensures that closed base changes are objects of the source site. I corrected the initially implicit slice identification by citing `lem-weil-pbc-proetale-restriction-injectives`; only its first sentence, not its injective/derived clauses, is used. I expanded the elementary open-immersion-implies-weakly-etale check using the actual open, flat, and weak-etale definitions. Arbitrary affine opens are used, without assuming a finite affine cover of X.

Step 4 uses precisely the arbitrary-base-change conclusion of `lem-pc-quasi-compact-base-change`, followed by the definition of a quasi-compact morphism applied to the affine open W itself. The open-subscheme description verifies that the resulting source is the complement of the closed pullback. Nothing is inferred from images of weakly etale maps being open.

Step 5 uses local lifts from Step 2 and refines their covering over the affine scheme Z_W. The identity Z_W over itself is a basis object, so the finite-refinement clause of `lem-weil-pbc-ind-etale-basis` applies with no extra finiteness assumption on the original lifting cover. The slice statement makes this the same covering as the one in the original Z-site. Refinement arrows actually restrict the chosen sections, and weak-etale composition ensures they can be evaluated by G and H. No proof-internal construction of a cited node is used.

Step 6 checks all four hypotheses of `lem-exc-closed-cover-extension`: W affine; Z_W closed; its complement quasi-compact by Step 4; the closed-fibre covering finite, affine and ind-etale by Step 5. Its statement explicitly supplies both specified reductions, so the direct-image formula identifies the images of the chosen lifts with restrictions of the original section. The remaining reductions are empty, and the sheaf axiom on the empty covering gives the zero sections used there. This proves local lifts rather than wrongly claiming global surjectivity of sections on an affine.

Step 7 applies the already established local criterion, then carries an arbitrary short exact sequence to a short exact sequence using its kernel and its epimorphism. I expanded the finite-limit/finite-colimit conclusion: kernel-image factorization gives preserved cokernels, and the displayed finite diagram difference maps give all finite limits and colimits. The cited exact-sequence, exact-functor and abelian-category definitions are exactly the notions used; there is no uncited theorem hidden behind an assertion that exactness follows formally.

Against delivery-errors B1-B10: no new unsplit/proof-carrying child or leaf is created; the original self-contained statement is unchanged; actual definition nodes replace the conventions collection; JSON TeX has one decoded backslash; sources name exact labels/tags; all searches ran; blueprint fields are filled; and the matching source theorem is rejected as a finished attachment because of its transitive sorry. Against C1-C8: every substantive external input is cited, every cited statement was opened, the 30 verbatim quotes were checked against those statements, and generic off-unit tools are declared only in `split_report.tool_uses`. A dependency traversal of the reused basis, localization, covering-extension, stability, operations and forgetful-functor nodes found no path back to this item. Against D1-D5: the seven steps carry the local lifting argument themselves; no conclusion or clause is moved into a child, and all intermediate sections and covering refinements are described. Against E1-E7: the hypotheses checked above cover the source and target sites, arbitrary base change, affineness, finiteness and specified fibre maps; no statement dispute or source error was found in the item.

Small cases checked: Z empty (every pushed-forward section is zero, so complementary members suffice), Z=X (the complement is empty and the lifted closed covering alone suffices), W empty (empty covering and the unique zero section), the zero coefficient ring, zero sheaves, empty finite closed-fibre coverings, and non-quasi-compact X (all tests remain local over affine opens). Nilpotents in the closed ideal cause no change: the covering-extension theorem supplies the scheme-theoretic closed-reduction isomorphisms, not merely equality of point sets. These checks require no new hypotheses.

## What could not be finished

Nothing in the one-level stage-1 split remains unfinished. The cited existing nodes remain their own items; no new child is created. This sandbox is to be handed to a fresh second reader after the required dry run. No push is authorized in this worker turn.


## Second reading by Q04

- Item statement: compared hypothesis by hypothesis with the unchanged main-20261015 blueprint statement and Stacks `proetale.tex`, Tag 09BM, label `lemma-closed-immersion-complement-retrocompact-exact`; PASS. Retrocompactness of the open is precisely quasi-compactness of its inclusion. Modules reduce to abelian sheaves by Tag 03DA. No statement dispute or extra hypothesis.
- Step 1: checked the actual section formula of `def-weil-pbc-proetale-operations` and sectionwise kernels of `def-weil-sheaf-of-modules-category` against the paragraphs preceding Stacks Tag 03DA; PASS after adding the sectionwise biproduct calculation, which justifies finite products and left exactness explicitly.
- Step 2: opened both the forgetful-functor node and the general-site local-surjectivity node; checked their exact hypotheses against Tags 03DA, 03CN(5), and sites Tag 00WM. The pro-etale site's universe convention supplies smallness and sheafification; PASS. No etale-only criterion is used.
- Step 3: opened every one of its eleven cited node statements; checked arbitrary closed base change, affine closed fibres, open immersions being weakly etale, the weakly-etale slice-site statement, and basis coverings against the actual hypotheses. PASS after citing `def-weil-pbc-ind-etale-basis` explicitly and identifying its full subcategory. Local affine reduction and transitivity apply to arbitrary X.
- Step 4: opened `lem-pc-quasi-compact-base-change`, `def-weil-finite-type-morphism`, and `def-weil-open-immersion`; the arbitrary base change of the quasi-compact complementary inclusion has quasi-compact source over affine W. PASS; neither X nor U is assumed globally quasi-compact.
- Step 5: opened all six citations and checked the finite-refinement clause over the affine base Z_W, where its identity is a basis object. PASS after adding the explicit basis-definition citation. Refinement restricts the original lifts; the resulting maps to Z remain weakly etale.
- Step 6: opened all four citations, especially the entire statement of `lem-exc-closed-cover-extension`, and compared its specified closed reductions with Stacks Tag 09BK, label `lemma-closed-immersion-affines`. PASS after replacing the instruction to transport a section by the actual formula t_a = r_a^*g_a and its naturality calculation. Affine, closed, quasi-compact-complement and finite affine ind-etale hypotheses all hold. Empty-fibre sections lift by zero.
- Step 7: opened the exact-sequence, exact-functor and abelian-category definition nodes; independently checked image factorization, cancellation by the preserved epi onto the image, and the finite diagram difference-map formulas. PASS after writing the cokernel universal-property argument. This is elementary abelian-category algebra, not an uncited appeal to exactness.
- New nodes: none; the entire argument reuses existing statements, with no item clause moved into a child. New Mathlib leaves: none.

Changes and reasons:

- Added the existing affine ind-etale basis definition as a citation in Steps 3 and 5, so the term basis is explicitly tied to its defining node; updated proof_deps and the two verbatim citations. citations.json now has 32 entries, each checked against the current cited statement.
- Added the biproduct calculation in Step 1 and explicit cokernel calculation in Step 7 to remove implicit categorical reasoning.
- Replaced Step 6's instruction to transport g_a with pullback along the specified reduction isomorphism and the equality proving it is a lift.
- Corrected source.external from broad section Tag 09A9 to exact Tag 09BM and label, with Tag 03DA for module coefficients. This supersedes the first worker's historical note that the source field was untouched; no statement or maintainer-owned field was changed.
- Ran independent Mathlib searches with a more general exact-functor phrasing through msearch.py (LeanFinder, Loogle, grep); recorded their actual results. Read the general Mathlib finite-colimit and epi-plus-kernel lemmas at ExactFunctor.lean:80 and Abelian/Exact.lean:313. They support the elementary Step 7 calculation but do not prove closed-immersion exactness without Steps 3–6, so the item is not a Mathlib leaf. No unavailable result was recorded as absence.

The current blueprint's two covering-lift paragraphs are realized by all seven steps. I read the unit/chapter records and the current unit statement: this auxiliary input and its route are unchanged; no SGA argument is used. The matching slopmaster2 theorem at ClosedImmersion.lean:178 still calls the epi lemma that uses the sorry counit at lines 66–68, so it supplies no finished attachment. I traversed each reused dependency's statement/proof dependency graph and found no path back to this item. No off-unit tool approval was installed; the existing split_report.tool_uses entries remain proposals for the maintainer.

Small cases independently checked: Z empty, Z=X, W empty, the zero ring and zero sheaves, an empty closed-fibre covering, a field (the two possible closed underlying subsets), nonreduced closed fibres, and non-quasi-compact X. The specified reductions are scheme-theoretic, and all finiteness is local over affine W. No additional finiteness on module sections or Noetherian hypothesis is used.
