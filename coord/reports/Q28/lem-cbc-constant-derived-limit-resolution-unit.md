# Q28 stage-1 delivery

Item: lem-cbc-constant-derived-limit-resolution-unit. Date: 2026-10-21.

## Files written

- dag/nodes/sec-smooth-purity/lem-cbc-constant-derived-limit-resolution-unit.json: statement, split into six proof steps; not a Mathlib leaf.
- citations.json: ten step/node entries, each checked as a verbatim substring of the cited statement.
- report.md: this report.

No new nodes and no new Mathlib leaves. The existing item statement, provenance and inherited Mathlib searches were retained. The sandbox initially contained only dispatcher briefs, without a node, report or search log; the node was copied from the live read-only repository. All writes are in the assigned sandbox. No Lean was written and no compiler, Lake or local DAG/preflight checker was run.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag, constant tower, derived-limit unit, constLimAdj and derived unit terminology found no declaration giving this item. In particular CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_unit_app_Qh_obj (CategoryTheory/DerivedCategory/AdjunctionUnit.lean) concerns two exact functors, rather than deriving the generally nonexact tower limit; DerivedLimitEventuallyIso.lean concerns the first right derived limit of towers of abelian groups. Neither states this item.

## WANTED

None. All sources needed for this split are available locally.

## Audit and changes

The item had no proof. Its blueprint source invokes completed pullback without spelling out the auxiliary constant-tower map's naturality. The completed-pullback definition does explicitly prescribe this map. I supplied its coordinatewise argument and descent, marking proof_origin.by as agent. No statement dispute, change of hypotheses, chapter change or unit-route replacement is needed.

No existence theorem for resolutions is invoked in the proof: a functorial resolution is fixed in the item's hypotheses. I read Stacks injectives.tex, Theorem 079P (theorem-K-injective-embedding-grothendieck), which provides the source context. I did not assume that this resolution functor is additive or commutes with shifts on complexes. Its functoriality and natural augmentation are exactly what the coordinate calculation needs.

The item uses the completed coefficient sheaf A_T throughout, not the constant sheaf with underlying ring A. The tower is a complex in the abelian category of strict inverse sequences, not merely a collection of objects and transitions in the derived category. The total derived inverse-limit realization and its natural localization comparisons are fixed by the statement; proving that realization exists is the already separate prop-weil-pbc-rlim-functoriality. Its use as a general tool is declared in split_report.tool_uses. No exactness of countable products or ordinary inverse limits is required here.

## Searches and reuse

The exact item was searched with the required logged msearch command: two LeanFinder phrasings, Loogle for CategoryTheory.Localization.liftNatTrans, grep for liftNatTrans|natTrans.*[Ll]ocaliz|constLimAdj, and LeanSearch for descent of natural transformations through localization. All five services answered; the results were read and recorded using the exact query texts from searches.jsonl. I retained the five preexisting search records rather than claiming those inherited searches as my own runs.

LeanFinder returned ordinary nonnegative right-derived-functor and objectwise injective-resolution formulas. Loogle and LeanSearch returned generic localization results. I read Mathlib/CategoryTheory/Localization/Predicate.lean:300-342 (especially liftNatTrans and liftNatTrans_app), Mathlib/CategoryTheory/Limits/HasLimits.lean:592-602 (constLimAdj), and Functor/Derived/Adjunction.lean:95-109 (derivedη and its factorization). These cover tools or require a derived-adjunction setup and its identification; they do not give the entire projection-defined strict-tower statement by one-line specialization. The existing localization DAG leaf supplies the needed descent theorem, so there is no new leaf or duplicate.

Whole-DAG statement searches for natural transformation/localization, functorial K-injective resolutions, and the projection-defined constant-tower map found the existing localization and module-limit nodes. tools/blueprint_refs.py ancestor identifies lem-cbc-completed-extension-zero-comparison; searches for constant tower, constant-tower, localization, and derived-limit unit found no blueprint node stating this item. The completed-pullback definition prescribes the construction but does not prove its naturality; the intrinsic-completeness and tower-class nodes have additional completeness/coefficient conclusions. blueprint.same_as remains empty, and the existing ancestor and via chain are retained. No new node was necessary, hence no duplicate pairs require a Not duplicates section.

## Review by Q28

I read the chapter sec-smooth-purity and unit sk-prop-sf-cbc records, the current main-20261015 proof of lem-cbc-completed-extension-zero-comparison, and the full statements of all eight distinct cited nodes. This split expands the auxiliary map needed in that proof's completed-pullback invocation; it does not replace the finite-to-complete CBC route. The statement agrees with the projection formula for the map in def-weil-pbc-completed-pullback. Stacks 079P is resolution-existence context, not a claimed source for a naturality theorem that its statement does not contain. The actual naturality argument is marked agent-written.

Step 1 uses lem-weil-pbc-module-sheaves-limits-sectionwise. Its statement gives exactly the compatible-family sheaf, coordinate projections, existence and evaluation of small limits for modules over an arbitrary ring sheaf. I checked its source, Stacks sites-modules.tex, Lemma 03DB (lemma-limits-colimits) and Lemma 03CO (lemma-limits-colimits-abelian-sheaves), part (2), including the first paragraphs of their proofs. The positive-integer inverse index category is small in the chosen site/module universes. The step explicitly constructs the differential and H(u), so it does not silently use exactness of limits. This is the imported limit theorem followed by coordinate computations, marked non-elementary because of that theorem.

Step 2 uses that same module-limit statement and def-weil-inverse-system. The latter's statement says precisely that a tower morphism commutes with transition maps. With identity transitions on the constant tower, the augmentation components form the necessary cone. The written section formula gives the map, its A_T-linearity, restriction compatibility, chain-map equation and uniqueness. This is an elementary application of the cited construction, not a new lemma.

Step 3 uses the coordinate limit statement again. The equality J(Delta f)_n a_C,n = a_D,n f comes from the natural augmentation that is fixed in the hypotheses. The displayed three equalities check the two composites after every coordinate projection. Joint monicity is immediate from the compatible-family description in the cited statement. No compatibility of unrelated resolutions, derived cones or homotopy-limit projections is asserted. This step is elementary.

Step 4 uses lem-weil-tower-category-levelwise-abelian for short exactness levelwise, lem-weil-pbc-exact-functor-derived-factorization for exact functors' termwise derived comparison and preservation of quasi-isomorphisms, and prop-weil-pbc-rlim-functoriality for the total derived inverse-limit functor realized by the stipulated J. I checked all three statements. The constancy functor is exact because each level has the original exact sequence. The fixed localization comparison is a natural comparison of functors, not an arbitrary list of object isomorphisms; the step writes its composite beta explicitly and checks invertibility of B(s) by conjugating the image under GQ of a quasi-isomorphism. No right exactness of lim is assumed. This is non-elementary and reuses the exact-functor and Rlim tools already in the DAG.

Step 5 uses def-weil-abstract-derived-category, which explicitly localizes complexes at quasi-isomorphisms, and clause (2) of lem-weil-pbc-localization-universal-property, which explicitly gives descent of NATURAL TRANSFORMATIONS under fixed natural comparisons. I read Categories Lemma 04VG (lemma-properties-left-localization): it gives factorization of functors but not, by itself, the natural-transformation clause. That clause is instead expressly in the cited DAG leaf, with Mathlib Localization.liftNatTrans and liftNatTrans_app, whose source I read. The proof supplies the categories, both inverting functors, both descended functors and the transformation tau, so every hypothesis is instantiated. All derived morphisms are covered by that theorem; no chain-map representative for an arbitrary derived morphism is assumed. This is non-elementary.

Step 6 uses def-weil-pbc-completed-pullback only for what its statement actually says: the specified canonical map factors the compatible component maps of a tower K-injective resolution through its ordinary inverse limit. The formula of Step 2 and the localization comparison of Step 5 are exactly that prescription. Naturality follows from the transformation constructed in Step 5. The identification is elementary and does not borrow a theorem about completed pullback from the definition.

For the small cases, I checked C=0 (even if the chosen resolution of zero is a nonzero acyclic complex, the components from zero are zero), a complex supported in one degree, an acyclic unbounded complex, the identity chain map and the empty scheme. Coordinate formulas remain valid in all cases; the acyclic case is handled by the fixed derived realization and localization, not by claiming that lim preserves quasi-isomorphisms on arbitrary tower complexes. There is no bounded-below, finite-generation, product-exactness or nonempty-scheme restriction. The argument never claims the unit is an isomorphism. All six proof steps are under 900 characters, so none hides a long inline auxiliary argument. Each used fact is either the quoted statement of an existing node, a stipulated hypothesis, or the explicit elementary coordinate calculation.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against these files and sources. There are no new statement-only nodes to audit under B1, no clause relabelled as a new lemma, and no new source tag needing a node. A graph reachability read confirmed that none of the cited localization, limit, exact-functor or Rlim tools depends back on this item. citations.json quotes were asserted against their exact live node statements. No mechanical check substitutes for the source and hypothesis checks above.

## Unfinished work

None within this one-level split. The required server dry run and direct push follow this report; their final results are reported by the delivery command.
