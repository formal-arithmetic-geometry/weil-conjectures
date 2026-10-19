## Files written

- `dag/nodes/sec-six-functors/lem-coef-left-fibration-dependent-sum.json`: statement unchanged; split into ten steps, using existing nodes only. Not a Mathlib leaf.
- `citations.json`: 26 exact statement excerpts, one for every step/node pair.
- `report.md`: this report. No new DAG nodes or Mathlib leaves. No unit record changed.

## Attachments

None. Searched the whole read-only WeilConjectures source for the exact item id, left fibration/LeftFibration, dependent sum and unstraightening, and dag/lean_names_upstream.json for the same notions; no project declaration states this item. The upstream master sorry declarations are not used as finished proofs.

## WANTED

WANTED: Jacob Lurie, Higher Topos Theory, Sections 2.1.3, 2.1.4 and 2.2.3 (especially Lemma 2.1.3.3 and Corollary 2.2.3.14), for lem-coef-left-fibration-dependent-sum. Read online at https://www.math.ias.edu/~lurie/papers/HTT.pdf; no archival copy located under literature/.

WANTED: Denis-Charles Cisinski, Higher Categories and Homotopical Algebra, Theorem 7.5.18, Corollaries 7.5.20 and 7.6.13, for lem-coef-left-fibration-dependent-sum. Read online at https://cisinski.app.uni-regensburg.de/CatLR.pdf; no archival copy located under literature/.

The agent-written application is marked proof_origin.by = agent. No matching Stacks tag states covariant straightening or coherent fibrant-slice localization; no tag is invented. No SGA source is used.

## Issues found and corrections

There was no sandbox item or report to resume, only searches.jsonl. I read its results and reused the relevant logged searches rather than repeating their questions. Kept the repository item's original statement, searches, ancestry and created metadata. The import had no proof. Its source points to Section 5 of On the tensor product of enriched infinity-categories (arXiv:2311.13362v1), a context for the algebroid application rather than a proof of the general slice theorem. I opened that source and supplied the general argument from the existing straightening and Brown-slice statements instead.

The inherited blueprint description referred to tuple left fibrations in the ancestor's paragraph 2. The actual main-20261015 ancestor proof, now filed under sk-thm-sf-package, has the RHom/inverse-limit adjunction comparison in paragraph 2, not an explicit tuple-fibration construction. The item's from.place and split_report now distinguish that historical root from the inherited algebroid dependency branch. The fixed chapter, unit and via list are untouched; this is foundational infrastructure below the unit, not another biduality proof. No target or node statement is changed, and there is no statement dispute.

A potential gap in an informal proof is that the Brown slice over E_F initially detects weak equivalences over B, while straightening on E_F detects them over E_F. Step 3 explicitly proves their equality by applying the Kan-fibration fiber criterion over each F(b). Another gap would be using an ordinary slice instead of the coherent slice: step 5 explicitly cites the coherent localization theorem, retaining triangle homotopies and higher simplices.

## Unfinished work

None for this stage-1 split. Existing unsplit dependencies remain their owners' items. No Lean was written, compiled, or built; no live repository or launcher file was edited, and no git command was run in the shared repository.

## Not duplicates

No new nodes. Whole-blueprint searches using tools/blueprint_refs.py for `left fibration`, `dependent sum`, `slice model`, and `slice equivalence` returned zero blueprint nodes. A whole-DAG concept search found and reused the existing covariant presentation, contravariant fibration criterion, Brown slice calculus, coherent model localization, Kan fiber criterion, and Brown pullback localization. None was recreated. A dependency-closure traversal found no path from any proposed cited dependency back to this item.

## Review by Q14

I read the item, its chapter and unit records, SETUP's three levels, GOAL, dag-sync, the worker brief and delivery-errors B–E. For the historical ancestor I read the main-20261015 proof at sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md. I read the statements of every cited node. For the main mathematical input I read HTT's left-fibration/Kan-base lemma and the fibration criterion between right fibrations, and Cisinski's coherent slice localization and the nearby explanation that fibrant slices localize to slices. The ordinary opposite-category argument uses the covariant model structure as its existing presentation states; it does not claim that opposites preserve the simplicial enrichment. Sources are online, with WANTED above for archival copies.

Step 1 uses def-coef-infinity-fibrations only for its precise horn ranges. The two consecutive fillers prove closure under composition; pairing a filler with the prescribed base simplex proves pullback stability. These are elementary, including the inner-horn claim about the total quasicategory.

Step 2 uses simplicial-right-fibration-presentation for the covariant model structure and its fibrant objects, contravariant-fibrations-between-right-fibrations for the right-fibration criterion (applied over the opposite base), and brown-slice-fraction-calculus for the exact list of Brown hypotheses being verified. Pullbacks and factorizations stay in the fibrant subcategory: a fibration to a fibrant object has fibrant domain. Neither the base nor E_F is assumed Kan. The derived covariance is an ordinary model equivalence, as required by the cited presentation.

Step 3 uses right-fibration-space-fiber on opposites, so both maps over (E_F)_b are Kan fibrations; kan-fibration-arbitrary-base-fibers then detects weak equivalences by their e-fibers. The presentation explicitly detects covariant weak equivalences by b-fibers and by e-fibers, respectively. These statements, rather than mere definitions of fibrations, justify comparing the two weak-equivalence classes. I checked that the strict fiber over e is identical whichever successive pullback computes it, and that every vertex of E_F lies over a vertex of B.

Step 4 uses the presentation's all-cofibrant assertion and the model-nerve-localization statement's explicit assertion about localizing the ordinary fibrant subcategory. Its resulting coherent nerve is exactly the left-fibration infinity category in space-transport-classification. The latter gives actual mapping complexes and an equivalence of whole infinity categories, so step 4 is not just a bijection of isomorphism classes.

Step 5 uses brown-slice-fraction-calculus for the canonical equivalence of coherent slices; all its hypotheses were checked in step 2. The left side has the correct weak equivalences by step 3. Space-transport-classification supplies the classifier equivalence used on the right. Restriction of an equivalence to a slice is written explicitly by its inverse and counit; the same unit/counit provide the triangle coherences. The canonical slice functor sends q to q as an arrow over B, establishing that the equivalence is the assignment in the item, not an unrelated equivalence.

Step 6 uses the Brown theorem's essential surjectivity for strict fibration representatives of coherent arrows, right-fibration-space-fiber's homotopy-fiber assertion on opposites, and classification's coherent mapping/base-change clauses for the family and its transports. I checked that q_b has Kan base F(b); no assertion that B itself is Kan is made. Opposite reverses horn indices; the constant-path fiber comparison is carried back with reversed paths.

Step 7 uses classification's restriction and fiber clauses and again the Kan-base theorem. The displayed integral is the total space of the restricted family, exactly as the item defines it, so this step does not silently import a colimit formula. Its map to F(b) is q_b itself.

Step 8 uses the presentation's fiberwise criterion to show pullback preserves weak equivalences, model-nerve-localization's entire-functor universal property to descend the strictly commuting square, and classification's base-pullback clause to identify restriction. The formula is equality of successive pullbacks on all simplicial parameters; the coherence is inherited from the tuple identities, not asserted from pointwise equivalences alone.

Step 9 uses classification's actual Kan mapping complex to represent F' to F by a strict map E_F' to E_F. It then uses brown-fibrant-localization-pullbacks, whose statement concerns the entire pullback cone and is natural in maps of squares, to compute the coherent pullback. Its fibration leg is q, as required, while the other leg need not be a fibration. Model localization's universal property makes this independent of representatives. This generic Kan-base theorem is an off-unit tool and is declared in split_report.tool_uses; no route step is replaced.

Step 10 uses the same Brown pullback theorem for product cones (products are pullbacks over the terminal object) and classification for the resulting external products. The coordinate formula (q times r) followed by (p times p2) equals (pq) times (p2r) in every degree, so it identifies the maps and higher transformations. The empty and point cases follow from the actual constructions.

There are no new statements needing B1–B8 checks or new-node searches. For the item's Mathlib question, I read the saved search results (ordinary Grothendieck constructions, ordinary fibered categories and sigma equivalences), kept the imported searches and appended the relevant real sandbox records. The focused additional grep located compAsSmallFunctorEquivalence; I read Mathlib/CategoryTheory/Grothendieck.lean:318–346. It changes the universe of an ordinary category-valued Grothendieck construction; it cannot supply this space-valued coherent slice theorem. No full match was promoted to a leaf.

Small cases checked: empty B (only empty total space, terminal functor categories); B a point and F empty (only the empty object over F); B a point and F a point (the construction is the identity on spaces); a discrete two-point F (a pair of fibers with disjoint total space); F=BG for a group (the family retains monodromy, not a bare family indexed by components); zero fibers of G; identity q and identity base changes; product with an empty family. None requires nonempty or discrete fibers. Universes remain small for all total spaces and finite products, with functor categories in the containing universe. All ten steps are below 2000 characters; none hides a lemma in a long step. The corrections described above address C1/C4 and the coherent-slice issue directly, without adding an item-clause node.

### Continuation review, 2026-10-17

The resumed worker retained the earlier split, citations, search records and report, and began with the required dry run. I compared the sandbox item against the current shared node: only worker-owned split fields differ, and its statement is identical. I reread the current statements of all nine cited dependencies and checked every one of the 26 citation excerpts against them; all remain verbatim. The project-source search for the item id and the notions LeftFibration, left fibration, dependent sum and unstraightening again found no attachment. I read the saved search results and Mathlib/CategoryTheory/Grothendieck.lean:318–346 rather than repeating the searches.

I reopened HTT online at Lemma 2.1.3.3 and Corollary 2.2.3.14 and Cisinski at Theorem 7.5.18 and Corollary 7.6.13, including the discussion of fibrant slices in Proposition 7.6.16. The hypotheses and the canonical functor there agree with steps 2–5: the ambient covariant model structure gives the Brown factorization axioms; the base-fiber comparison in step 3 makes the two weak-equivalence classes equal; the slice theorem retains the coherent triangles. I reread Section 5 of the enriched tensor-product source and the current main-20261015 ancestor proof, which support the distinction already recorded between the application and this generic foundational argument.

In step 10 I replaced the ambiguous phrase “the projections” by the actual maps $p\times p_2:E_F\times E_{F_2}\to B\times B_2$ and $q\times r$. Projections of total spaces onto separate factors need not be left fibrations when those factors are not Kan, and the proof requires only these product maps and products inside the fixed-base Brown category. Coordinatewise lifting proves precisely the needed assertions. No new theorem or dependency is introduced. The empty-base, empty-value and point-base cases still hold, and every step remains below 2000 characters.
