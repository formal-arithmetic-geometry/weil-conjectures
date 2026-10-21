# Stage-1 delivery: lem-per-adic-common-stage-truncations

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-adic-common-stage-truncations.json: statement, split into nine proof steps; not a Mathlib leaf. The statement and its statement dependencies are unchanged. Filled the proof, dependency union, agent proof provenance and split report, and appended actual Mathlib searches.
- report.md and citations.json: worker review and 35 verbatim statement quotations, one for every cited node in every step.
- searches.jsonl is the search tool's own log. The PDF text extracts and write_split.py are sandbox working material, not delivered node files.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None for this item. Searched the project under lean/WeilConjectures for the blueprint id and for common-stage, scalar/truncation and t-exact terminology; no project declaration gives the entire assertion. The general comparison infrastructure does not establish coefficient t-exactness or the bounded t-structure and heart on this completed-coefficient pair category.

## WANTED

None. All sources used are present.

## What needed correction

The item was unsplit, with empty proof and proof dependencies. No mathematical change to its statement was necessary. Its phrase “degree-zero cohomology H^r” means the degree-r cohomology object placed in degree zero, namely (tau^{ge r} tau^{le r} K)[r]. Step 4 spells this out.

Bhatt–Scholze Proposition 6.8.14 does not itself print the associator equations for this project's raw rationalized pair presentation. The proof is therefore explicitly marked agent-written. It uses the existing completed coefficient comparison and constructible transport statements, rather than identifying this category without proof with another coefficient convention. In particular, it never computes arbitrary integral truncations by termwise truncating the reduction tower: that requires additional Tor compatibility, absent here.

The functor descent proposition prop-weil-pbc-descent-functors assumes triangulated-exact functors. Truncation generally is not such a functor. I did not cite that proposition for truncation descent; step 7 proves its arrow formula directly. The common-stage heart is also not obtained by presuming that one chosen finite representative lies in both halves: step 9 realizes both witnesses and their inverse equations at one finite enlargement.

## What could not be finished

Nothing remains in the authorized stage-1 split. No Lean was written and no compiler, Lake or build was run. The independent maintainer review remains part of the normal delivery process.

## Not duplicates

No new nodes were created. The generic fact initially considered for extraction is already covered by lem-weil-pbc-triangle-morphism-extension, clauses (1) and (2), so it is cited instead. The Mathlib searches found triangle_map_exists, triangle_map_ext and triangle_iso_exists, but there is no reason to create another leaf for a statement already present in the DAG.

The blueprint search for truncations found prop-constructible-truncations. That statement fixes finite-field data k_0=F_q and k its algebraic closure and includes an automorphism-pullback assertion. The present item works over any field with ell invertible and specifies the completed integral/raw rationalized presentation and its coherent pair formulas. It is not an equivalent statement, so blueprint.same_as remains []. Likewise the fixed-pair truncation statements concern equivariant objects, rather than coefficient-stage pairs. The blueprint ancestor query returns lem-per-smooth-pullback-t-exact, and the inherited exact first-paragraph place and via chain are retained. The current main-20261015 proof and the chapter/unit records were read; this is ordinary-cohomology infrastructure below that route, not a replacement of any unit step.

## Review by Q76

I read Bhatt–Scholze, Propositions 6.8.11(3) and 6.8.14, in the local PDF text (printed pp. 60–61). These give the bounded-cohomology perspective and coefficient descent motivating the item; the proof's completed-coefficient identifications come from the cited project statements. I also read BBD Proposition 1.3.3 on pp. 29–30, the t-exactness definition 1.3.16 on p. 36, and Proposition 1.1.9/Corollary 1.1.10 on pp. 23–24. The former characterizes the truncation adjunctions and whole triangle, and the latter explains the connecting-map uniqueness. There are no new-node sources to check.

For step 1 I opened lem-cbc-compactification-geometry-fibre-bound: its first assertion really gives source Noetherianity and finite dimension from the finite-type map to Spec k, and its last sentence preserves invertibility. Spec k satisfies its base hypotheses directly. I read the full statements of prop-weil-pbc-integral-tstructure and prop-weil-localized-tstructure: they apply to precisely these completed categories with compatible etale-origin witnesses, and give bounds by ambient cohomology, localization of the halves, and boundedness. I read prop-weil-pbc-scalar-extension, which specifies integral change of completed rings followed by localization and the exact scalar functors. The hypotheses at every coefficient field are unchanged.

For step 2 I checked that lem-weil-finite-free-completed-scalar-comparison asserts finite freeness of the actual completed sheaf S over R, not merely finite freeness of constant valuation-ring sheaves; it also identifies ordinary derived tensor with the completed scalar functor and says its value is complete. I checked lem-pur-derived-change-of-rings for computation by a K-flat resolution, and lem-weil-pbc-finite-free-constructible-scalar-transport for preservation of the selected constructible categories including compatible etale witnesses. The cohomological-bound argument is written out on the underlying finite direct sum of complexes. It does not infer exactness from a definition of flatness or cite a mere local model as a global calculation.

For steps 3 and 4 I read the complete statement of lem-pod-texact-truncation-comparison. Its hypotheses are bounded t-structures and an exact functor preserving both halves at every cutoff; steps 1–3 supply these, and it states the normalizing unit/counit equations, naturality for arbitrary transformations between such functors, identity and composition. Applying its transformation clause to the specified associator gives exactly the equation written in step 4. The shift compatibility is genuinely supplied by prop-weil-pbc-scalar-extension, not inferred from the truncation lemma. The two comparisons followed by that shift give the degree-zero cohomology comparison. I read def-weil-derived-cohomology-sheaves for its ambient kernel/image meaning, together with the localized truncation comparisons to interpret its rational version.

For step 5 the cited triangle-morphism lemma is used only in clause (2). Its hypothesis is Hom(A[1],B')=0, where A is the first term in the mapped truncation triangle and B' the last term in the target triangle. The shift convention gives A[1] in degrees at most r-1 and B' in degrees at least r+1, so finite-stage orthogonality applies. Its conclusion explicitly includes the boundary equation d'h=f[1]d. This prevents loss of the shifted third-arrow clause. Both comparison components satisfy its two square hypotheses by their normalized equations.

For step 6 I read the pair-category definition and prop-weil-pbc-common-stage-calculus: arbitrary morphisms are common-stage representatives and finite diagrams and equalities are realized at one field. These statements, together with scalar t-exactness proved here, let finite-stage orthogonality kill any representative. I read thm-weil-pbc-verdier-axioms: it states that this very pair category is triangulated, every j_E is exact, and the identifications j_F T_{F/E} = j_E are exact natural isomorphisms. Thus the finite-stage triangle supplies the truncation triangle, and each object's own finite-stage bounds supply boundedness. No faithfulness, conservative scalar extension, or global uniform amplitude was used.

For step 7 I checked the exact transport formula u_N=a_{N,M,F} T_{N/M}(u) a_{N,M,E}^{-1} in def-weil-pbc-finite-stage-pair-category. Substituting the step-4 coherence and naturality equations gives precisely the displayed refined representative. Equal representatives therefore remain equal; the middle comparison factors cancel for composition. The step proves this calculation instead of claiming a descent theorem outside its hypotheses. For step 8 the maps are their finite-stage units and counits. Common-stage calculus descends their equations, and the full triangle calculation of step 5 descends the connecting square as well. Orthogonality in the now-established pair t-structure verifies the same hypothesis of the triangle-morphism lemma, identifying these with its canonical truncations.

For step 9 I included the two isomorphisms witnessing half membership, both inverses, and both inverse equations in the finite diagram. The common-stage calculus statement really includes all these equations. Thus one field N makes T_{N/E}K isomorphic to an upper and a lower finite-stage object at once. The finite-stage heart and canonical truncation maps identify it with its H^0. The exact identification j_N T_{N/E}=j_E then gives the claimed pair isomorphism. The reverse heart inclusion follows directly from the definitions of the halves.

I checked the small cases E=L (the comparison equation reduces to identity), X empty and the zero object (every bound and representative calculation still applies), one-degree objects and shifts (H^r is placed in degree zero), and a heart object whose two half witnesses use different fields (step 9 handles it without reflection of bounds). A basis is used only to establish vanishing in step 2; all comparison maps are the basis-independent normalized maps, so neither chosen bases nor a chosen truncation cone enter the formulas. The stage calculus handles nonfaithful inclusions as well. No proof step exceeds 2000 characters. Each cited node was read for its statement, and citations.json copies those statements verbatim; no source tag or definition node substitutes for an unproved non-elementary assertion.

The B–E checklist was checked against the files: there is no unsupported new object or lemma, no clause relabelled as a node, no use of another node's proof in place of its statement, and no coefficient-category identification or extra Tor hypothesis. All Mathlib records appended here are queries actually run with msearch.py; searches.jsonl retains the results and the report above explains why the generic triangle hits are not a match for the whole item. Off-unit results are declared only in split_report.tool_uses as general coefficient/category tools. The maintainer-owned top-level tool_uses field was not changed.
