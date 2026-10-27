## Worker report

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-field-lisse-stratified-heart-support.json (statement, split, no Mathlib match), citations.json, report.md. No new nodes and no Mathlib leaves. All eight steps cite existing nodes.

Attachments: none. Searched lean/WeilConjectures by the item id and lisse, constructible, condensed and weakSerre, including SixFunctors/ProEtale/ConstructibleSheaf.lean and ModuleObject/. The former concerns discrete fixed coefficients and contains a sorry in its comparison theorem. No declaration states all clauses of the item. The closed common-refinement declarations are reused through their existing node.

WANTED: none.

The statement is unchanged. In particular its explicit hypothesis on lisse kernels, cokernels and extensions remains; no unconditional theorem for arbitrary condensed coefficients is asserted. The imported created.item ancestry has no blueprint ancestor: blueprint_refs.py ancestor prints None. The null ancestry is retained and the exact source proof places recorded in blueprint.from.place and split_report.blueprint.

Nothing remains unfinished in the split. Existing unsplit dependencies remain items of their own. No Lean was written or compiled, no Lake/build tool or direct git command was run, and all writes are in this sandbox.

## Sources and searches

Read the current-blueprint sk-lem-coefficient-heart/sk-lem-coefficient-heart.proof.md (1), its sk-lem-coefficient-heart-common-stratification.proof.md (1)--(3), and sk-thm-sf-pf-field/sk-thm-sf-pf-field-tensor.proof.md (1). They give common refinement, exact restriction and the final stratum-extension membership assertion. The expanded general-coefficient conditional proof is marked agent-written.

Read Stacks proetale.tex Tag 09BM, lemma-closed-immersion-complement-retrocompact-exact, including its retrocompact-complement hypothesis; sites-modules.tex Tag 03DJ, lemma-extension-by-zero-exact; and WeilConjectures/ConstructibleSheaf/Refinement.lean lines 141--184 (actual fibre-product domains). No SGA source was used.

Whole-DAG searches covered common refinement, exact restriction, open/closed exactness and support, scalar bases and lisse/constant local models. Whole-blueprint searches used blueprint_refs.py for stratification, closed immersion, lisse, finite dimensional, constructible kernel and extension locally closed. The E/Qbar-only coefficient-heart nodes are insufficient for arbitrary Lambda, so the proof reuses general tools instead.

All Q101 Mathlib searches used msearch.py and are logged in searches.jsonl: two LeanFinder phrasings of stratified closure/support, LeanSearch for locally closed extension constructibility, Loogle for Constructible/kernel, and two greps for constructible Serre/lisse extension and extensionByZero/constructible. The hits concern finite-type/quasicoherent modules, free sheaves, ordinary function extension or constructible subsets. None states this internal-module sheaf assertion. Both greps and Loogle gave zero hits; services responded successfully. Inherited searches remain untouched.

## Not duplicates

No new nodes. E/Qbar-specific det-lem-coefficient-heart-common-stratification and new-det-lem-coefficient-heart-common-stratification-lisse are not cited as arbitrary-Lambda results. Existing exactness, finite scalar transport and support nodes are reused rather than recreated. lem-sfb-coefficient-heart-locally-closed-extension is used for its Noetherian-subshemes/quasi-compactness assertion, not to replace this item's constructibility clause.

## Review by Q101

I read the source proofs and all cited node statements, checking the following mathematical uses. This direct-delivery self-review leaves the independent maintainer review separate.

Step 1: lem-weil-pbc-vector-space-free gives a basis. Finite generation, supplied by the stated finite presentation, makes it finite by the written finite-support argument. The final flatness-independent clause of lem-sfb-constant-finite-free-presentation-extension explicitly transports a specified scalar isomorphism F^r to V into R_T^r to its scalar extension, including r=0. def-sfb-lisse-coefficient-module and sk-def-sfb-constructible then give both directions of the model equivalence. The condensed ring itself is never identified with its discrete scalar field.

Step 2: lemma-constructible-common-refinement supplies a common refinement and its existing closed Lean construction uses fibre-product schemes. lemma-constructible-pullback-stratification explicitly provides the base-changed strata; the two projections are consequently actual morphisms. def-weil-pbc-proetale-site supplies the covering condition. lem-sfb-scalar-matrix-inverse-image explicitly states the finite-power regular-module comparisons e_r for arbitrary morphisms and arbitrary condensed rings. sk-def-sfb-module-pushforward-pullback states composition of inverse images. Thus base-changed trivializing covers give lisse restrictions. No scheme factorization is inferred from set-theoretic image containment. Boolean closure gives constructible intersections.

Step 3: det-prop-sfb-module-pullback-exact-main states finite-limit and finite-colimit preservation for every condensed ring and every scheme morphism. lem-sp-exact-functor-preserves-homology (a) explicitly identifies pulled-back kernels and cokernels. The hypothesis on lisse closure applies on these locally closed scheme strata, so Step 1 and sk-def-sfb-constructible give the conclusion.

Step 4: the same pullback exactness and lem-sp-exact-functor-preserves-homology (c) restrict the ambient short exact sequence. The lisse-extension hypothesis supplies the middle restriction; there is no unproved local simultaneous-splitting assumption. The definitions sk-def-sfb-constructible and def-sfb-lisse-coefficient-module justify zero and isomorphism closure, including empty X.

Step 5: lem-sfb-coefficient-heart-locally-closed-extension explicitly states Noetherianity of locally closed subschemes and quasi-compactness of opens. This verifies the complement hypothesis of lem-sfb-proetale-identified-open-closed, whose statement explicitly supplies exact i_* and its actual invertible module counit. sk-def-sfb-coefficient-morphisms states invertibility of alpha_f for every condensed ring. The action definition in sk-def-sfb-module-objects identifies internal modules with sectionwise modules over the ring sheaf; the displayed tensor pullback and direct image in sk-def-sfb-module-pushforward-pullback are exactly the module-sheaf functors being used. def-sfb-module-open-lower-shriek explicitly states exactness of j_!, so no exactness property is extracted merely from a name.

Step 6: the closed counit and the explicitly stated inverse-image composition reduce the first two restrictions to j^*j_! and k^*j_!. lem-sfb-open-module-restriction-identities gives both, with the required quasi-compact open already checked. def-sfb-module-lower-star identifies underlying sheaves; def-sfb-finite-lower-star gives the exact fibre-product section formula; lem-sfb-proetale-open-restriction-counit identifies that formula with actual restriction to X minus Z for arbitrary coefficient rings. The fibre product is empty and its sheaf sections zero. There is exactly one action on the zero sheaf. This proves all three internal-module isomorphisms rather than just a support containment.

Step 7 is elementary assembly from earlier steps: def-constructible-stratification requires disjoint locally closed immersion domains covering X; these are precisely S, its closed complement in Z, and X minus Z. def-weil-constructible-subset states Boolean closure and the Noetherian locally-closed criterion. The supplied lisse and zero models meet sk-def-sfb-constructible on those actual domains. Empty pieces can be omitted.

Step 8: lem-sp-exact-functor-preserves-homology (c) shows preservation of quasi-isomorphisms. Localization as defined in sk-def-sfb-derived-categories gives descent, and direct termwise inspection of L[0] gives G[0]. This is in the ordinary derived category, without completion or a per-degree substitute for a derived isomorphism.

Small cases checked: empty X; empty S and complementary pieces; L=0; rank zero and ranks varying across covering objects; identity open/closed immersions; nonreduced strata; and a non-discrete condensed coefficient field. For S=X the claim reduces to L itself. For S closed or open one extension is an identity. No characteristic, connectedness, admissibility or invertibility assumption is inserted.

Checked delivery-errors B--E: no new nodes with proofs hidden in their statements; existing dependencies and verbatim citations; every non-elementary functor assertion has a node stating it; no item clause moved to a new node; exactness and quasi-compactness checked at their uses. Each proof step is below 2000 characters. During drafting I replaced the inapplicable E/Qbar-only common-stratification citation with actual fibre products and the general scalar-matrix comparison. The chapter/unit route is retained; off-unit general tools are declared in split_report.tool_uses. No statement dispute or source correction was necessary.

Final citation audit: Step 2 now explicitly cites lem-galois-fpqc-covering-base-change (the existing Mathlib leaf) for fpqc base-change stability and lem-weil-pbc-weakly-etale-composition-base-change for stability of weakly etale arrows. I opened both statements: together they give precisely base-change stability of the pro-etale trivializing covering. This replaces the former reliance on the covering definition alone. No new nodes were needed.
