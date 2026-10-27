## Worker report

1. Files written:
   - dag/nodes/sec-six-functors-basics/lem-sfb-stack-qcqs-composition-affine.json: item, split; not a Mathlib leaf.
   - dag/nodes/sec-six-functors-basics/lem-sfb-space-quasiseparated-test-calculus.json: one new statement-only algebraic-space lemma, unsplit; no Mathlib match.
   - citations.json: one exact statement quotation for every node in every step's uses list; report.md and searches.jsonl contain the review and actual search evidence.
2. Attachments: none. Searched lean/WeilConjectures for the exact blueprint tag, qcqs composition, AlgebraicStack and ArtinStack. No project declaration covers the item. Sorry declarations were not treated as proofs.
3. WANTED: none. All sources used are present in literature/stacks-project/.
4. The statement is retained verbatim, including the absence of finiteness and absolute-diagonal assumptions. Its empty proof was the missing work. The algebraic-stack definition requires BOTH quasi-compactness and quasi-separatedness of its representable relative diagonal; the scheme definition alone does not give that assertion. The proof now handles both.
5. Nothing remains unfinished in this one-level split. The new supporting statement is intentionally unsplit and proof-free for subsequent stage-1 work. No Lean, compiler, Lake, repository write, git command, SGA route, or sub-agent was used.

## Proof route and searches

Read GOAL.md, the three levels in SETUP.md, the chapter and unit records, and the current latest blueprint chapter, unit, and direct-images proof. The ancestor command prints a null blueprint ancestor, as already stored in the item. The inherited long from.place and via describe the adequate-moduli prerequisite chain; this split refines that chain below the unit, without changing a unit or chapter route. The current latest direct-image proof has no separate stack permanence argument to replace.

Whole-DAG tag and statement searches, project-source searches, and blueprint_refs.py searches for 050W, 03KQ, 03KM, 03KL, 03KK, algebraic stack, algebraic spaces, quasi-separated stack, and quasi-separated morphisms of algebraic spaces were read. The broad quasi-separated blueprint search returned scheme and cohomological results, not this space calculus. Existing lem-sfb-algebraic-stack-qcqs-permanence assumes absolute source and target conditions; it cannot prove composition without adding hypotheses. Existing stack-separated composition nodes concern proper diagonals. They were not used as substitutes for quasi-separatedness.

All Q149 Mathlib searches are the actual msearch.py calls in searches.jsonl. The new node has two semantic phrasings, Loogle, LeanSearch, and source grep. Read the returned hits, then Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean:46-52 and 116-130, Affine.lean:43-59, and Separated.lean:119. Their endpoints are Scheme. Generic diagonal-property instances do not supply algebraic spaces, intrinsic space compactness tests, or algebraic stacks as a one-line specialization. Retained the item's earlier Q14 searches and appended the present searches. There were no unavailable services. No Mathlib leaves were created.

The new node is a genuine smaller input: it concerns ordinary morphisms of sheaves of sets (algebraic spaces) and a single diagonal compactness condition. It does not assert either clause of the item for arbitrary stacks, and says nothing about affine stack maps. Quasi-compact composition was NOT made a new node: it is written directly from test objects and the fibre-product definitions. The space-separated-implies-quasi-separated implication is included with the usual separation calculus, rather than made a separate elementary node.

## Review by Q149

I read Stacks stacks-morphisms.tex 050U (definition-quasi-compact), 050W (lemma-composition-quasi-compact; proof omitted), 050K (lemma-composition-separated; diagonal factorization and its space-property inputs), 050H (lemma-fibre-product-after-map; cartesian square), 050T (lemma-characterize-representable-quasi-compact), 04YW(4) (definition-separated), 04YT (lemma-representable-quasi-separated-diagonal-quasi-compact), and 0CHQ (definition-affine). For the affine scheme input I read morphisms.tex 01S7 (lemma-affine-separated). For the new node I read spaces-morphisms.tex 03KM (lemma-separated-local), with the quasi-separated axiom and equivalence (1) iff (2); 03KL (lemma-base-change-separated); 03KQ (lemma-composition-separated); and 03KK (lemma-trivial-implications). These statements apply to arbitrary algebraic spaces, with no separation or finiteness condition on the base. The new statement has no proof sketch hidden in it.

For step 1, I opened def-sfb-stack-qcqs-morphism: its test is an arbitrary quasi-compact algebraic stack, not just an affine scheme. I opened lem-sfb-algebraic-stack-fibre-products, which asserts that both iterated products are algebraic stacks and identifies them by their triple construction, and def-sfb-stable-pointed-moduli-groupoids, which explicitly defines the objects and arrow condition of a 2-fibre product. The step gives the functors, inverse, and natural isomorphism, so it uses no unproved associativity slogan. Quasi-compactness survives this equivalence because the same quasi-compact smooth scheme atlas is transported. This is a few-line argument from the cited definitions and statement; it is the sole elementary step.

For step 2, I opened lem-sfb-fibred-groupoid-representable-smooth-calculus: its statement really preserves algebraic-space representability under arbitrary base change and composition, without requiring atlases for the base-changing category. I opened lem-sfb-representable-stack-quasicompact-tests: both directions of the equivalence between intrinsic space scheme tests and stack quasi-compactness are present. The triple definition justifies the identification of scheme tests after base change. Applying step 1 to the representable maps and then the reverse test equivalence obtains precisely intrinsic space quasi-compactness of the composite tests; it does not assume a scheme test has scheme source.

For step 3, I opened lem-sfb-representable-pullback-over-space: it explicitly allows any algebraic space mapping to the target, not only a scheme chart. It supplies the space U_T over the possibly nonschematic space V_T. The new node's scheme-test criterion then applies to p_{V_T}, because every such scheme test is an original scheme test of p; its composition clause applies to p_{V_T} and r_T. Both maps, not their absolute sources, have the required quasi-separatedness. The association of triple products identifies their composite with the desired test. This avoids importing the scheme-only Mathlib result or assuming quasi-separated absolute sources.

For step 4, I opened lem-sfb-groupoid-diagonal-two-pullback-identities, whose clause (2) states exactly the square needed with u=v=f and h=g. It gives the base-change description of i, rather than merely a fully faithful or diagonal definition. The previously established representable-property arguments make i and its composite with Delta_f qcqs on every scheme test. The object formula identifies that composite with Delta_{gf}. The definition from def-sfb-stack-qcqs-morphism then gives stack quasi-separatedness, including the second-diagonal compactness condition.

For step 5, I opened lem-weil-pbc-affine-morphism-permanence: clause (1) gives scheme affine base change and clause (3) gives separatedness. I opened lem-sfb-space-affine-locality: the statement gives separatedness of affine space morphisms and representability over scheme targets. Its compactness clause uses affine scheme tests; the separate atlas argument added in the resumed review below proves the intrinsic all-quasi-compact-space predicate required here. The actual affine scheme tests meet its affine definition after every further affine test, so its conclusion is being used on the same objects. The new node explicitly says separated space maps are quasi-separated. The already read 050T node then gives stack quasi-compactness of q. Finally, def-weil-closed-immersion explicitly includes the affine-local quotient-ring characterization, so its affineness claim is available in the statement, not only its proof.

For step 6, I checked the orientations: the test has alpha:q(x1) -> q(x2), and A_T is formed using q(x1). Hence the second section uses alpha^{-1}, and its arrow condition is exactly q(beta)=alpha. The lift and inverse written in the step identify the test with the equality locus of these two sections. Clause (1) of the diagonal-pullback node gives the same base-change square; it does not require q to be separated. The affine scheme permanence statement supplies separatedness of A_T -> T; its ordinary diagonal is therefore a closed immersion. I opened lem-weil-pbc-closed-immersion-base-change: it permits an arbitrary scheme map, exactly the pair-of-sections test here. The closed-immersion definition makes this test affine, so step 5 gives both intrinsic space properties. Thus every diagonal test is a scheme and is qcqs; no claim that an arbitrary stack diagonal is a monomorphism was used.

I checked small cases before finalizing: the empty stack and empty test scheme (the empty atlas remains quasi-compact); identities (the relative diagonal is an equivalence even for a stack with a non-quasi-compact absolute diagonal); non-quasi-compact targets (all tests are local, and no finite global affine cover is chosen); a non-DM stack such as B G_m (the representable diagonal may be a positive-dimensional space); and affine maps with no finite-type assumption. For the new node, identities and empty spaces satisfy all clauses; the criterion is relative to the target and does not mistakenly assert absolute quasi-separatedness. None of the proofs assumes that intersections of affine opens are affine. Every non-elementary result is a cited node; every citation was checked against its statement and has a literal quotation in citations.json. All six steps have fewer than 2000 characters, and none moves an unproved comparison into an adjective. No statement dispute or mathematical source error was found.

## Not duplicates

lem-sfb-space-quasiseparated-test-calculus vs lem-a1-space-monic-diagonal-tests: identifies equality-locus tests for a monomorphism into a scheme-base change; it gives no quasi-separated composition or intrinsic scheme-test criterion.

lem-sfb-space-quasiseparated-test-calculus vs lem-a1-space-separated-lqf-permanence: requires separated locally quasi-finite maps and open restrictions; the new lemma allows arbitrary quasi-separated space maps and gives composition and scheme-test equivalence.

lem-sfb-space-quasiseparated-test-calculus vs def-sfb-presheaf-map-separated-diagonal: only defines separatedness of a presheaf map by closed-immersion tests; it is not a quasi-separatedness theorem.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-flat-space-derived-pushforward-base-change: existing statement concerns flat algebraic-space derived pushforward and base change; it does not state the relative quasi-separatedness scheme-test equivalence or composition closure for arbitrary space morphisms.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-hilbert-graph-family-base-change: existing statement concerns closed hilbert graph families and arbitrary base change; it does not state the relative quasi-separatedness scheme-test equivalence or composition closure for arbitrary space morphisms.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-locally-separated-closure-equivalent-images: existing statement concerns locally separated targets identify closure-equivalent geometric points under stronger or different hypotheses; it does not assert the arbitrary quasi-separated space-morphism scheme-test criterion and composition.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-locally-separated-rational-point-closed-immersion: existing statement concerns rational points of locally separated algebraic spaces are closed immersions, with closed-immersion or closed-subset hypotheses; the new result is about arbitrary relative quasi-separated morphisms.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-noetherian-space-finite-scheme-cover: existing statement concerns finite separated noetherian scheme cover of a separated noetherian algebraic space under stronger or different hypotheses; it does not assert the arbitrary quasi-separated space-morphism scheme-test criterion and composition.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-qcqs-space-fibre-product: requires three absolute qcqs spaces and concludes an absolute product is qcqs; the new lemma assumes only relative quasi-separated morphisms.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-representable-stack-fppf-locality: existing statement concerns fppf target tests for representable stack morphisms; it does not state the relative quasi-separatedness scheme-test equivalence or composition closure for arbitrary space morphisms.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-scheme-colimit-upgrade-space-targets: existing statement concerns criterion for a scheme colimit to have algebraic-space targets; it does not state the relative quasi-separatedness scheme-test equivalence or composition closure for arbitrary space morphisms.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-separated-space-homeomorphism-affine: existing statement concerns separated universal homeomorphisms of algebraic spaces are affine under stronger or different hypotheses; it does not assert the arbitrary quasi-separated space-morphism scheme-test criterion and composition.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-affine-locality: concerns affine maps; quasi-separated maps need not be affine or separated, and the new scheme-test/composition assertions are absent.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-closed-immersion-quasi-coherent-modules: existing statement concerns quasi-coherent modules and ideals along a closed immersion of algebraic spaces, with closed-immersion or closed-subset hypotheses; the new result is about arbitrary relative quasi-separated morphisms.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-closed-subset-finite-fibre-open: existing statement concerns finite-fibre base open for a closed subset in a proper algebraic space, with closed-immersion or closed-subset hypotheses; the new result is about arbitrary relative quasi-separated morphisms.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-descend-closed-immersion: existing statement concerns closed immersions of algebraic spaces descend along affine inverse limits, with closed-immersion or closed-subset hypotheses; the new result is about arbitrary relative quasi-separated morphisms.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-descend-separated: existing statement concerns separatedness descends to a stage for a finitely presented algebraic space under stronger or different hypotheses; it does not assert the arbitrary quasi-separated space-morphism scheme-test criterion and composition.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-diagonal-locally-finite-type: existing statement concerns the relative diagonal of an algebraic-space morphism is locally of finite type; it does not state the relative quasi-separatedness scheme-test equivalence or composition closure for arbitrary space morphisms.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-etale-atlas-topological-dimension: existing statement concerns topological dimension of a quasi-separated space is computed by an etale scheme atlas, including after base change, not quasi-separated composition and the intrinsic scheme-test criterion.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-etale-maximum-degree: existing statement concerns bounded fibres and the maximum-degree open of an affine etale atlas, not quasi-separated composition and the intrinsic scheme-test criterion.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-eventually-fibre-dimension: existing statement concerns eventual geometric fibre dimension bound for finitely presented algebraic spaces, not quasi-separated composition and the intrinsic scheme-test criterion.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-eventually-proper: existing statement concerns eventual properness of finitely presented algebraic spaces and requires properness (or proves it); it does not give the scheme-test criterion and composition for arbitrary quasi-separated space maps.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-fibre-dimension-base-change: existing statement concerns geometric fibre dimension bounds for algebraic spaces survive base change, not quasi-separated composition and the intrinsic scheme-test criterion.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-finite-fibre-quasifinite-criterion: existing statement concerns finite field fibres and quasi-finiteness along a fibre, not quasi-separated composition and the intrinsic scheme-test criterion.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-four-property-fppf-descent: treats affine, finite type, quasi-finite and separated, not arbitrary quasi-separated maps.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-fp-qcqs-source: requires a finitely presented map over an absolute qcqs target and concludes an absolute qcqs source; it does not state relative quasi-separated composition or detection.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-henselian-proper-clopen-lift: existing statement concerns lifting a proper clopen fibre part over a henselian pair and requires properness (or proves it); it does not give the scheme-test criterion and composition for arbitrary quasi-separated space maps.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-hom-representability: existing statement concerns representability of the relative morphism functor for algebraic spaces; it does not state the relative quasi-separatedness scheme-test equivalence or composition closure for arbitrary space morphisms.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-integral-extension-qc-open: existing statement concerns extension of an integral space across a quasi-compact open; it does not state the relative quasi-separatedness scheme-test equivalence or composition closure for arbitrary space morphisms.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-integral-qcqs-permanence: existing statement concerns quasi-compactness and separation for integral algebraic spaces; it does not state the relative quasi-separatedness scheme-test equivalence or composition closure for arbitrary space morphisms.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-locally-separated-base-change: requires an immersion diagonal, not a quasi-compact diagonal; these are different conditions, and it has no quasi-separated scheme-test criterion.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-proper-base-change: existing statement concerns proper morphisms of algebraic spaces are preserved by base change and requires properness (or proves it); it does not give the scheme-test criterion and composition for arbitrary quasi-separated space maps.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-proper-cancellation: existing statement concerns properness cancellation for algebraic spaces and requires properness (or proves it); it does not give the scheme-test criterion and composition for arbitrary quasi-separated space maps.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-proper-composition: existing statement concerns composition of proper morphisms of algebraic spaces and requires properness (or proves it); it does not give the scheme-test criterion and composition for arbitrary quasi-separated space maps.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-qcqs-source-products: concludes absolute quasi-separatedness of sources and qcqs products under absolute hypotheses; it does not give composition or scheme-test detection for arbitrary relative quasi-separated maps.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-relative-ampleness-fpqc-descent: existing statement concerns relative ampleness of spaces descends fpqc locally; it does not state the relative quasi-separatedness scheme-test equivalence or composition closure for arbitrary space morphisms.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-relative-dimension-base-change: existing statement concerns geometric fibre dimension bounds for algebraic spaces under base change, not quasi-separated composition and the intrinsic scheme-test criterion.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-representable-proper-tests: existing statement concerns intrinsic properness of representable algebraic-space maps is tested on schemes and requires properness (or proves it); it does not give the scheme-test criterion and composition for arbitrary quasi-separated space maps.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-separated-fp-composition: gives separated or finitely presented composition. Arbitrary quasi-separated maps need not be separated or locally finitely presented; its statement has no quasi-separated test criterion.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-stack-etale-local-qcqs-homeomorphism: has the stack predicate requiring a qcqs diagonal and covers by representable etale maps. The new lemma has the intrinsic algebraic-space predicate requiring only a quasi-compact diagonal, gives arbitrary-scheme-test equivalence, and proves its composition closure.

lem-sfb-space-quasiseparated-test-calculus vs lem-trf-ample-scheme-test-line-preparation: existing statement concerns line-module preparation on an arbitrary scheme test of a locally polarized space; it does not state the relative quasi-separatedness scheme-test equivalence or composition closure for arbitrary space morphisms.

lem-sfb-space-quasiseparated-test-calculus vs lem-trf-space-qc-separated-etale-local: proves locality of quasi-compact AND separated maps, not locality and composition of quasi-separated maps.

lem-sfb-space-quasiseparated-test-calculus vs lem-trf-space-section-algebra-etale-base-change: existing statement concerns the section algebra of a line module on a space restricts correctly to etale bases; it does not state the relative quasi-separatedness scheme-test equivalence or composition closure for arbitrary space morphisms.

lem-sfb-space-quasiseparated-test-calculus vs lem-trf-space-separated-affine-chart-overlap: existing statement concerns affine overlaps of affine charts of a separated space over an affine base under stronger or different hypotheses; it does not assert the arbitrary quasi-separated space-morphism scheme-test criterion and composition.

Existing lem-sfb-space-quasicompact-affine-tests and lem-sfb-space-quasicompact-fppf-local supply compactness facts only; they do not supply quasi-separatedness. Existing lem-sfb-space-diagonal-scheme-tests supplies representability, local finite type and monomorphism of a space diagonal, not its compactness or the new separation calculus. Existing stack separated-composition nodes and absolute stack qcqs-permanence were also checked and do not state the new input.

lem-sfb-space-quasiseparated-test-calculus vs lem-sfb-space-qcqs-permanence: the existing result assumes an absolute quasi-compact source and quasi-separated target, whereas the new relative calculus assumes neither and gives scheme-test detection and composition.

## Resumed review by Q149

The required first dry run of the existing sandbox completed successfully at f291570b6ff. I compared the item with the current repository: its statement and imported metadata agree, and no repair note exists. I read the saved searches and their returned declarations, rather than repeating their unchanged questions.

A fresh reading of every cited statement exposed a compactness-predicate mismatch in step 5: lem-sfb-space-affine-locality defines quasi-compactness by affine scheme tests, whereas def-sfb-stack-qcqs-morphism quantifies over quasi-compact algebraic spaces. I repaired the proof by taking a quasi-compact etale scheme atlas U of each such space C. Affine permanence gives the scheme-quasi-compact map A_U to U. The precise statement of lem-weil-pbc-quasi-compact-morphism-preimage-qc-open applies with W equal to all of U, and gives its quasi-compact scheme source. The precise base-change clause of lem-trf-space-fibre-products-etale-covers supplies the surjective etale atlas A_U of A_C. This proves exactly the intrinsic compactness predicate, without assuming C is a scheme. The affine-locality node is now used for separatedness only, whose diagonal closed-immersion predicate agrees verbatim with the new node.

The additional citations have literal statement quotations in citations.json. The space fibre-product lemma is declared as an off-unit generic tool; the scheme inverse-image lemma is an existing Mathlib leaf. No new node or new search was needed. I also filled the new node's two none-state lean_audit entries required by the brief. The new space calculus remains statement-only. The inherited statement, sources and searches are retained. All proof steps remain below 2000 characters.
