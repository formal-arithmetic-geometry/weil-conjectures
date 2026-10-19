# Worker report: lem-cbc-dense-hypercover-set

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-dense-hypercover-set.json`: statement, split; no Mathlib match for full simplicial hypercovers. Eight proof steps, no new nodes.
- `citations.json`: one entry for every use in every proof step, with a verbatim quotation from the cited statement.
- `report.md`: this report. `research.json`, `searches.jsonl`, and `write_split.py` are sandbox research artifacts, not delivery node files.

## Attachments

None. Read-only searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, dense hypercovers, and bounded hypercovers found no project declaration of this statement. The existing formal attachment statements are reused as DAG tools, not claimed as attachments of this item. The upstream master checkout was not treated as proof evidence.

## WANTED

WANTED: Dugger--Hollander--Isaksen, Hypercovers and simplicial presheaves, arXiv:math/0205027v2, Definition 6.1, Lemma 5.4, Proposition 5.5, Section 6.5 and Proposition 6.6, for lem-cbc-dense-hypercover-set. This PDF is absent from the local literature directory; I read the specified arXiv PDF online without downloading it. The proof is marked agent-written, with its local supporting source Stacks hypercovering.tex and its online construction source specified in every relevant step. No Choudhury--Gallauer result is needed.

## Findings and corrections

The item already stated the correct arbitrary-site theorem, and its statement is unchanged. There were no proof steps. The main risk is applying a finite-family or fibre-product hypercover theorem on this arbitrary sieve site. I avoided that inference by reading the *statements* of the generic formal-family attachment operators and splitness criterion; neither has a finite-index or finite-limit hypothesis. Matching objects and all local lifts are formed in presheaves. The formal-family realization requires no limits in the site and is justified directly by evaluating a natural transformation at the identity arrow.

The original source's Proposition 6.6 suppresses cardinal bookkeeping and refers to the induction of Proposition 5.5. The split now spells out a single infinite bound mu, its regular successor kappa, the matching-section bound, at most mu covering-sieve arrows per section, the proper degeneracies added at the next degree, and the countable union bound. It also proves the map into the original hypercover, rather than merely constructing some small hypercover of the target. All isomorphisms chosen for the final representative set are over the fixed target.

Read the chapter and unit records, the current main-20261015 compactification proof of thm-cbc-finite-level-proetale, and the item's recorded ancestry. The small hypercover set is a supporting construction below that route. No unit realization fields needed editing: this item is not the unit's key statement.

## Not duplicates

No new nodes. Searched the whole DAG and `blueprint_refs.py search` for hypercover, split simplicial, skeleton, and cell attachment, and searched DAG sources for Tags 017P, 0DAU and 0DAV. The already existing `lem-cbc-presheaf-sheafification-epi-local-lifts` supplies the exact arbitrary-topology presheaf criterion; it was reused. The finite-basis existence and finite-extension nodes assume fibre products or finite limits and finite index sets, and cannot supply the present induction. The more primitive `lem-weil-pbc-site-split-attachment-operators` and `lem-weil-pbc-site-split-attachment-split` have no such hypotheses and were reused. No blueprint node duplicates the full bounded dense-set statement, so `blueprint.same_as` remains empty.

## Mathlib searches

Every recorded query was run through the required msearch.py command and appears in searches.jsonl. The item was searched by natural-language queries in both LeanFinder and LeanSearch, Loogle's Hypercover/Small pattern, and source grep. Hits concern zero- or one-hypercovers, not full augmented simplicial hypercovers. Read Mathlib Sites/Hypercover/Zero.lean:855-885 and Sites/DenseSubsite/OneHypercoverDense.lean:135-180 to check that difference. Two distinct natural-language phrasings were tried. Additional genuine searches for split extension produced skeleton/Kan-extension definitions and simplicial-set skeleton union statements, not the whole extension theorem; those searches helped find the existing generic DAG tools and did not cause a new node. Read Mathlib SimplicialObject/Basic.lean's sk/cosk adjunction interfaces and Split.lean's Splitting definition to confirm their scope.

## Review by Q110

I read DHI arXiv:math/0205027v2 online at Definition 6.1 (p. 16), the generalized-cover lifting construction of Lemma 5.4 (pp. 13-14), the split extension in Proposition 5.5 (p. 14), and the cardinal argument in Proposition 6.6 (pp. 18-19). These allow a small site with matching presheaves and do not require a subcanonical topology or fibre products in the site. I also read Stacks hypercovering.tex, Tags 0DAU and 0DAV, including the final omitted-composition paragraph, and simplicial.tex, Tag 017P. I do not cite 0DAV's hypercover-existence statement on the present site: that statement assumes fibre products. Instead I use the DAG's extracted generic attachment statements, whose exact text and recorded Lean signatures quantify over any category and arbitrary family index types. No SGA source is used.

Step 1 uses only the universe already fixed in the statement and explicit cardinal counting. The regular-successor argument is written out, rather than assuming that countable unions preserve a possibly countable bound. Taking mu at least aleph_0 handles finite sites and all dimensions uniformly. A Grothendieck universe contains the successor of the chosen small cardinal. For the empty category the empty collection suffices.

Step 2 uses precisely the family and component-arrow description of `def-weil-pbc-formal-coproduct`. The identity-evaluation argument proves the full-faithful realization needed here in two sentences, so no general Yoneda lemma is silently used. In particular it constructs the formal boundary cones even though matching presheaves need not be representable.

Step 3 uses `lem-cbc-presheaf-sheafification-epi-local-lifts` in both directions: from the hypercover's sheafified matching epi to a covering sieve of actual lifts of id_T, and from the constructed map's covering local-lift sieves to a sheafified epi. I opened that node; its statement is for arbitrary Grothendieck topologies on small categories and explicitly excludes any need for fibre products or subcanonicity. Pulling back a sieve uses the axiom already in the item's statement, not a fibre product in the category.

Step 4 takes no hidden existence theorem: matching sections are compatible finite tuples of face sections. Thus their count is bounded by a finite product. At degree one the tuple includes the equality of the two augmentations, so the matching object is V_0 times_{h_T} V_0, not an unaugmented product. The number of test objects is bounded by the number of arrows via identities.

Step 5 uses the same local-lifting statement for the original U matching map, at the image of each matching section b. It chooses at most mu arrows for each of at most mu pairs (A,b). Each x is an actual section of U_{n+1}, so its boundary gives all the required compatibilities simultaneously. The converse part of the cited node proves the sheafified epi of Z to M; no unquoted preservation-of-epis or exact-sheafification theorem is used.

Step 6 uses exactly the three clauses of `lem-weil-pbc-site-split-attachment-operators`: an extension with strict old restriction, the new/old face formulas, and the normalized epi action with invertible components. These last clauses are exactly the hypotheses in the statement of `lem-weil-pbc-site-split-attachment-split`; that theorem supplies splitness and identifies the new nondegenerate indices. The proof then defines the refinement on new and degenerate summands and checks faces and epis explicitly. The factorization of finite order-preserving maps into their surjection onto their image and the inclusion of that image checks all remaining operators. The covering assertion follows again from the exact local-lifting criterion, since adding degenerate summands cannot destroy existing local lifts. The number of surjections out of a fixed finite ordinal is finite. These generic combinatorial tools belong to the proper-base-change unit; both are declared in split_report.tool_uses because this unit has no attachment construction. Definition nodes and Mathlib leaves need no such route exception.

Step 7 is an assembly argument: each operator and each identity is read at one sufficiently large finite stage, and the extensions are strict. Matching conditions also stabilize at a finite stage. No existence of a categorical infinite colimit or non-small limit is being assumed. The total bound uses countably many degrees and mu infinite.

Step 8 explicitly codes every bounded formal family and all its operators by small sets. Step 2 ensures those codes cover actual presheaf morphisms, including augmentations. Taking the subset satisfying the axioms, then representatives up to isomorphism over each target, is legitimate set formation; composing the chosen representative isomorphism with V to U gives the refinement with the required direction. It is not enough to select representatives without this last composition.

For edge cases, I checked an empty site, a finite site, a terminal site with its trivial topology (where one can select a vertex and its degeneracies), and a site admitting an empty covering sieve. In the last case the local-lift construction allows an empty new family: the sieve criterion still proves the required epi, and the generic attachment allows empty index sets. No nonempty matching-section set, no representability of matching objects, and no sections of a sheaf being objectwise surjective are assumed. These checks revealed no statement correction. There are no new statements needing additional small-case tests. I checked the cited nodes' dependency closures for a path to the item and found none, and checked each verbatim citation against its node statement before writing citations.json.

## Unfinished work

None in this one-level split. The existing attachment nodes remain responsible for their own downstream formalization; they are not replaced or split here. The second reader should scrutinize Step 6's generic application and refinement naturality against the quoted statements, and verify the dry-run result before delivery. This worker will not push.

## Second reading by Q110

- Item statement: checked against DHI Definition 6.1 and Proposition 6.6 (v2, pp. 16, 18–19), the Choudhury–Gallauer Fact 5.2 reference, and the arbitrary-site conventions in the cited DAG definitions; the hypotheses (small category, Grothendieck topology by sieves, no fibre products or subcanonicity), representability, matching maps, refinement over the fixed target, uniform cardinal bound, and representative-set conclusion all agree. The empty category, terminal/trivial site, a field-sized finite site, and an empty covering sieve introduce no omitted case.
- Step 1: checked the cardinal choice and regular-successor argument against DHI Proposition 6.6; the infinite bound handles finite and countable cases, the empty-category case is explicit, and the size claims are elementary.
- Step 2: checked the formal-family realization against `def-weil-pbc-formal-coproduct`; identity evaluation supplies the component and arrow, and all matching objects remain presheaf objects. Verdict: cited statement supports the construction; the two-line Yoneda calculation is elementary.
- Step 3: checked both applications of `lem-cbc-presheaf-sheafification-epi-local-lifts` against its full arbitrary-Grothendieck-topology statement and pullback-stability hypothesis; the sieve pullback supplies local lifts without representable pullbacks. Verdict: sound.
- Step 4: checked the matching-object cardinal estimate against the definition of proper matching faces and the finite products of lower degrees; the degree-one case is the fibre product over the augmentation, and object identities inject objects into arrows. Verdict: elementary and correct.
- Step 5: checked the local choices against the matching-map clause of `lem-cbc-presheaf-sheafification-epi-local-lifts`; every chosen section has the required boundary, and the triple-indexed coproduct has the stated bound. Verdict: sound, with no hidden representability or finite-limit assumption.
- Step 6: checked every use of `lem-weil-pbc-site-split-attachment-operators` and `lem-weil-pbc-site-split-attachment-split` against their statements, including strict restriction, boundary formulas, normalized proper-epi labels, component isomorphisms, and the new nondegenerate indices. The explicit face/epi naturality calculation and finite epi-label count discharge the remaining claims; the local-lift criterion justifies the matching epimorphism. Verdict: sound generic-tool use, recorded in `split_report.tool_uses`.
- Step 7: checked strict-stage assembly against the finite-stage simplicial identities and matching conditions; stabilization uses only finite stages, and the countable union remains bounded by the chosen infinite cardinal. Verdict: elementary and correct.
- Step 8: checked the coding and representative selection against the formal-family realization and the bounded-cardinal conclusion of DHI Proposition 6.6; the final representative isomorphism is explicitly composed with the refinement over the same target. Verdict: elementary set formation and correct density conclusion.
- New nodes: none. I searched the DAG and blueprint for hypercover, split-extension, matching, skeleton, and dense-set statements; the only required dependencies are the existing formal-coproduct definition, local-lift criterion, and the two generic attachment tools. No duplicate or Mathlib leaf should be created.
- Citation audit: every non-elementary dependency in steps 2, 3, 5, and 6 is cited by node id; the quoted text in `citations.json` was checked verbatim against each cited node statement. No step relies on a node's proof text or on an unquoted Stacks fact.
- Mechanical review: no Lean or compiler tools were run, as required for stage 1. The delivery preflight, DAG check, and split review dry run passed after this reading.

Changes made in this second reading: none to the item statement, proof, dependencies, citations, or node set; appended this hypothesis-by-hypothesis review and retained the worker's source and edge-case checks.
