# Stage-1 report: lem-coef-space-yoneda-density

## Files written

- `dag/nodes/sec-six-functors/lem-coef-space-yoneda-density.json`: statement, split; five proof steps. No new nodes and no Mathlib leaves. The statement and both statement dependencies are unchanged.
- `citations.json`: every node used by every proof step, with verbatim statement excerpts (full statements where several clauses are used).
- `report.md`: this report. The `search-*.txt` files preserve the seven actual search responses; `prepare_split.py` is sandbox-only preparation material.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id and for Yoneda and representable-presheaf terminology. The hits are ordinary category/sheaf or dg arguments, not the coherent space-valued assertion on arbitrary small quasicategories. The exact upstream master was also checked as reference material, not as evidence of a completed proof. The item has no `lean_audit` declarations to examine. No Lean was written and no compiler, Lake, build or local DAG-check tool was run.

## WANTED

WANTED: Jacob Lurie, *Higher Topos Theory*, March 10, 2012 text, sections 2.2.1 and 5.1.1, Corollary 3.3.3.4, and Lemmas 5.1.5.2-5.1.5.3, for lem-coef-space-yoneda-density. The PDF was read online at https://www.math.ias.edu/~lurie/papers/highertopoi.pdf; printed pp. 321-323 contain the item's two lemmas. It is not listed as obtained in `literature/LIST.md`.

WANTED: archival Kerodon pages Proposition 4.2.5.4 (0154), Corollary 4.7.3.22 (02J5), and Proposition 4.7.3.20 (02J2), for lem-coef-space-yoneda-density. All three were read online. These are Kerodon identifiers, not Stacks tags. The Stacks input actually used is Tag 08NS, `literature/stacks-project/simplicial.tex`, label `lemma-trivial-kan-homotopy`; I read that proof and its lifting input Tag 08NM, label `lemma-trivial-kan`.

The proof is marked `proof_origin.by = agent`: it expands the online source's evaluation argument and proves density by a coherent section/mapping-space calculation instead of reproducing HTT's deformation-retraction proof. No source was downloaded or written into the read-only repository.

## What was wrong or needed expansion

The imported item is true and its statement is unchanged. It was a statement-only obligation. Its source correctly identifies evaluation and density, but a citation of those same two conclusions would not split it. The existing full-faithfulness assertion in `lem-coef-infinity-yoneda-presheaf-limits` is insufficient to supply evaluation against arbitrary presheaves; I have not used it for that claim. I use only its separately stated colimit mapping-space criterion at the final step. During self-review I corrected that last citation, so the step does not assume an uncited identification of transformation spaces with mapping-space limits.

The essential distinction is between a presheaf's full small right fibration of elements and the ordinary category of its connected components. Taking only components would lose density already when C is a point and F has nontrivial higher homotopy. The delivered argument uses the former throughout. It also constructs an actual coherent cocone through the target-fixed-arrow right fibration, rather than independently choosing its vertex legs.

The blueprint ancestry is retained. I read the current main-20261015 exceptional-adjoint statement and separate proof as well as the historical master source, the chapter and the unit record. The underlying displayed finite mapping-complex adjunction has the same role in both snapshots. This item supports that paragraph through the existing localization/presheaf-presentability chain; no chapter or unit statement or route is changed, and this item is not the unit's key node.

## What could not be finished

Nothing remains in this one-level split. The existing generic coherent straightening statement is itself unsplit; this delivery cites its actual statement, and does not claim to prove that foundational theorem. There are no new children.

## Not duplicates

No new nodes were created. Whole-blueprint searches `space yoneda density`, `Yoneda`, `right fibration`, and `density`, and whole-DAG statement searches for Yoneda, right fibrations, straightening, and categories of elements were inspected. `lem-pc-yoneda` is ordinary set-valued Yoneda; `lem-coef-derived-enriched-yoneda` is dg-module Yoneda. Neither is this item. Instead of adding an element-fibration, final-object, restriction, section, or cocone criterion node, I reused the existing generic nodes or wrote the short exponential/pullback calculation as a proof step. `blueprint.same_as` remains empty.

## Mathlib searches

All seven added search entries were run with the required `msearch.py Q36 lem-coef-space-yoneda-density` command, and the exact query texts and actual responses are recorded. They include LeanFinder twice with distinct phrasings, Loogle, LeanSearch, a broad CategoryTheory grep, a focused declaration grep, and an AlgebraicTopology grep. All services returned successfully; none is recorded as unavailable or as a search that was not run.

I read the signatures of every returned semantic hit. I read the actual source of `CategoryTheory.yonedaEquiv` at `Mathlib/CategoryTheory/Yoneda.lean:724`, `CategoryTheory.Presheaf.colimitOfRepresentable` at `Mathlib/CategoryTheory/Limits/Presheaf.lean:290`, and its tautological variants at lines 669 and 692; I also read the ordinary density setup in `CategoryTheory/Functor/KanExtension/Dense.lean:35-64` and the quasicategory/StrictSegal hit sources. The ordinary `Category` and `Type` parameters cannot specialize to the full infinity category of spaces with coherent transformations. The standard-simplex Yoneda and singular/StrictSegal results concern ordinary simplicial sets. No hit is an exact match or one-line specialization, so `mathlib_match` stays null. The prior searches were preserved as inherited evidence; only the seven newly run queries are my new records.

## Review by Q36

I read delivery-errors B-E in full and checked the proof against the cited statements and the online source. The construction is deliberately small in the original universe, even though the presheaf and arrow categories are formed in the larger universe.

Step 1 uses the exact small-representative, mapping-space, pullback and representable-slice clauses of `lem-coef-space-transport-classification`. This node explicitly promises a small total representative when the base is small, rather than merely small fibers; that hypothesis is met because C and every F(c) are small. The proof writes the elementary inner-horn argument that E_F is a quasicategory, needed when it is used as K in step 3. `lem-coef-infinity-slice-right-fibration` supplies both the slice quasicategory and its right-fibration projection. `lem-cbc-enhanced-functor-cone-calculus` supplies the quasicategory structure of the functor category. No ordinary full-faithfulness result is used to infer evaluation.

Step 2 uses `lem-coef-infinity-slice-equivalence-final` at the identity, whose invertibility is part of the identity axiom. Its conclusion is exactly the finality needed by `lem-coef-infinity-terminal-anodyne`. The right-anodyne inclusion and the right fibration from step 1 meet the two hypotheses of `lem-coef-infinity-right-fibration-exponentiation`. Pulling its lifting problem back over the fixed projection keeps the base map fixed, so the restriction of over-maps is a trivial Kan fibration. I added the explicit citation of `lem-weil-pbc-trivial-kan-homotopy-equivalence` for the implication from this lifting property to an equivalence, rather than leaving it as an uncited topological theorem. I read Stacks 08NS and 08NM for this input. The same classification node says transport is pre/postcomposition and preserves the identity element, which is exactly what the written naturality calculation uses. Its full simplex-level comparison, not a pi_0 statement, is crucial here.

Step 3 proves the needed sections/limit fact in the item, rather than creating a node for a short consequence. The classification applied to the constant point makes the section simplicial set Kan. Applied over a point, it identifies maps of spaces with the Kan-complex mapping model; applied over K, it identifies maps from the constant T with over-maps K times T to Q. The middle exponential isomorphism is degreewise currying, explicitly written in the proof. It carries the evaluation cone to the displayed natural map for every T. Thus `lem-cbc-enhanced-functor-cone-calculus` gives the limit universal property directly. This step is marked elementary because the assertion follows by those three displayed maps and that cited criterion; it does not assume the substantial general straightening theorem without a node. Smallness of K and Q ensures the resulting section space is small. I checked the online HTT Corollary 3.3.3.4 against this formulation; the right-fibration version uses K opposite.

Step 4 uses the mapping-bifunctor and target-fixed-arrow clauses of the classification, which explicitly identify that right fibration and its identity compatibility. The pullback along h has fibers Map(h_c,F), already proved equivalent to small F(c). The inverse coherent evaluation equivalence therefore gives an over-map from the chosen small E_F to the arrow-fibration pullback. The mapping-space clause permits essentially small fibers, so no assertion that the larger arrow model is literally small is needed. Evaluation on that actual simplicial map gives E_F times Delta^1 to P(C), precisely a coherent transformation under the definitions. This repairs the potential gap of assembling vertex legs without their higher compatibilities. Only the auxiliary presheaf/arrow categories use a larger universe; the original E_F remains the density index.

Step 5 uses the same classification's composition/pullback compatibility to identify a map over C with a section of the explicit pullback right fibration over E_F. The map a to (identity,a) and its inverse projection work in every degree and on parameter simplices, so this is elementary and no theorem about ordinary categories of elements is imported. The section formula of step 3 is applied with K = E_F and H = G composed with p_F opposite; both are small as required. The evaluation equivalence of step 2 identifies the testing diagram. I checked the actual map, not just its endpoints: precomposing g with the cocone leg corresponding to (c,x) evaluates to g_c(x), the same as the over-map/section comparison. For the final inference I cite the explicit Map-to-limit criterion in `lem-coef-infinity-yoneda-presheaf-limits`, whose statement says precisely that a cocone is colimiting when this comparison is an equivalence for every testing object. This avoids silently importing a mapping-end formula from the weaker cone-calculus statement and proves the colimit of this very cocone. This verifies both the existence of the small presentation and its full coherent universal property.

I tested C empty (E_F empty, the unique presheaf is the initial object of the terminal presheaf category), C a point with F empty, C a point with F a non-discrete Kan complex such as a model of S^1 or BG, and F representable (its element slice has the identity as final object). For C a point the density diagram is indexed by the whole space F and is constantly the point; its colimit is F, which confirms the necessity of keeping higher simplices. In the section calculation, K empty gives the point as the empty limit, and K a point gives Q itself. No nonemptiness, finite cardinality, truncatedness, or existence of all presheaf colimits is assumed.

Every cited node was opened and its statement checked. `citations.json` has exact coverage of the step/node pairs and every quote is a verbatim substring. The proof dependencies equal their union. The two generic off-unit tools (coherent cone calculus and trivial-Kan homotopy equivalence) are declared only in `split_report.tool_uses`, with reasons; maintainer-owned `tool_uses` is untouched. I checked that none of the chosen dependencies depends on the item, and no new node restates a clause, hides the argument, duplicates another node, or requires missing hypotheses. There is no SGA citation, no statement dispute and no protected-field change.

## Validation

The preliminary server `srvcheck.py ... review_split` returned PASS with zero new nodes. A final dry run of `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q36 lem-coef-space-yoneda-density --no-push` is required on the final files. The worker reports READY only after that command prints OK and leaves those accepted files unchanged. No push is performed by this worker.

The first full dry run returned `OK (not pushed)` with preflight passed at `147bde7ec2`. Because the final citation and the explicit total-quasicategory argument were refined after that run started, the command is run once more against this final sandbox before READY.

## Second reading by Q36

- Item statement: checked against HTT Lemmas 5.1.5.2–5.1.5.3 and the stated universe/space conventions; every hypothesis and both evaluation and density clauses agree, including coherent higher transformations. Verdict: PASS.
- Step 1: checked against the full statement of `lem-coef-space-transport-classification`, the slice right-fibration statement, and the coherent functor-cone calculus; smallness, quasicategory, right-fibration, and mapping-space uses are present. Verdict: PASS.
- Step 2: checked against the final-object, right-anodyne, exponentiation, trivial-Kan homotopy, and transport statements; the identity edge, fixed-base pullback, and coherent naturality all have the required hypotheses. Verdict: PASS.
- Step 3: checked against the classification mapping formula and the dual cone criterion; the section/limit calculation includes the degreewise currying map and parameter simplices. Verdict: PASS.
- Step 4: checked against the classification's target-fixed-arrow and pullback clauses plus the cone conventions; the actual over-map supplies a coherent cocone and preserves the small index. Verdict: PASS.
- Step 5: checked against the classification pullback formula and the explicit colimit mapping-space criterion; the section identification is degreewise and the comparison is the map induced by the cocone. Verdict: PASS.
- New nodes: none; there were no new node statements to audit, and the existing dependency statements were reread for each cited use. Verdict: PASS.

Changes made in this second reading:

- Added this per-step and per-node audit so the review records the source and hypothesis checks explicitly.
- Made no mathematical or DAG changes: the item statement, proof steps, dependency list, citations, and search records already passed the B–E checks.
