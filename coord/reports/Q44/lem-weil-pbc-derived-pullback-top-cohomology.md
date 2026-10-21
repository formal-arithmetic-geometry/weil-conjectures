# Q44 stage-1 delivery

Item: lem-weil-pbc-derived-pullback-top-cohomology. Date: 2026-10-21.

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-derived-pullback-top-cohomology.json — statement, split into eight proof steps; not a Mathlib leaf.
- citations.json — one verbatim statement quotation for each dependency cited in each step.
- report.md — this report.

There are zero new nodes and zero Mathlib leaves. The local write_split.py is only a sandbox preparation script; searches.jsonl is the search tool's original log.

## Attachments

None. I searched the project WeilConjectures tree for the item tag, derived pullback/cohomology wording and the module comparison notion. Existing declarations define the comparison, establish it for flat modules or special locally free single-cohomology objects, and give composition/shift compatibility. None states all clauses of this item for arbitrary module sheaves and complexes without a lower bound. In particular exists_isDerivedModulePullbackComparison supplies a map, not this theorem, and canonicalSinglePullbackMap on invertible modules is insufficient.

## WANTED

None.

## Findings and changes

The imported statement is retained verbatim. No statement dispute or source error was found. The initial node had no proof. Its proof now uses the existing same-upper-bound flat replacement, rather than assuming the module category has enough projectives or imposing finite rank, quasi-coherence, flatness of g, or a lower cohomological bound. The cokernel calculation verifies the map specified in the statement, including its normalization. Composition is reduced to the existing canonical single comparison square with an identity side and then extended using naturality at a specific morphism v; no whole comparison c_g is inverted.

The proof is marked agent-written: the upper-bound/truncation argument follows the dual of Stacks 05TC, while the actual resolution calculation and the naturality/composition assembly are written out here. Sources read include derived.tex (05T7 lemma-subcategory-left-resolution, 05TC lemma-negative-vanishing, 08J5 remark-truncation-distinguished-triangle), homology.tex (0118 section-truncations), cohomology.tex (06YD lemma-bounded-flat-K-flat, 06YJ derived-pullback construction, 0D5S lemma-derived-pullback-composition), sites-cohomology.tex (06YS lemma-K-flat-resolution and its bounded-above inputs), and sheaves.tex (0096 lemma-adjoint-pullback-pushforward-modules, 0097 lemma-push-pull-composition-modules). I also read the project statements/docstrings in BoundedFlatReplacement.lean, DerivedPullbackComposition.lean, DerivedModuleBaseChangeMap.lean, DerivedModulePullbackComparison.lean, and the existing CanonicalSinglePullbackComparison/Square modules. These were source reads only.

The current main-20261015 ancestor thm-weil-pbc-direct-image-finiteness-proper states FIN and contains no proof section. The existing blueprint.from.place already identifies this item's intervening affine coherent comparison input and is retained. The chapter and proper-base-change unit routes are unchanged. No unit realization field belongs to this non-key item. Blueprint-wide searches for "top cohomology" and "derived pullback", and DAG concept searches, found no equivalent blueprint statement. The top-cohomology Serre pairing hit is about projective twists; it is unrelated.

## Mathlib search review

All new searches were run through msearch.py and are in searches.jsonl. I retained the inherited searches instead of rewriting their history. Two semantic phrasings were tried: the full sheaf-module theorem and the general right-exact derived-functor degree-zero description. Loogle with "leftDerived", "homology" gave no hits. LeanSearch returned ordinary sheaf pullback constructions. The relevant grep returned CategoryTheory/Abelian/LeftDerived.lean. I read its degree-zero construction around lines 269–315: its natural map uses projective resolutions, and leftDerivedZeroIsoSelf is an objectwise classical-derived-functor statement under HasProjectiveResolutions. Neither it nor the ordinary sheaf pullback hits gives this total derived sheaf theorem as a one-line specialization. No category of sheaf modules was silently assumed to have enough projectives. The extra grep concerning a leftDerivedLift factorization returned no hits and is recorded without claiming otherwise.

## Not duplicates

No new nodes were created. Existing lem-pc-derived-pullback-single-cohomology has local finite-locally-free and nonnegative-cohomology hypotheses, and does not replace this arbitrary upper-bounded theorem. lem-weil-pbc-ringed-tensor-cohomological-bounds provides scalar-extension bounds, not the normalized top-cohomology naturality and composition clauses. The existing canonical single comparison square is used as a tool rather than re-created.

## Review by Q44

I checked delivery-errors B–E against the actual node statements and the local source text. Because no new nodes are needed, there is no statement-only leaf, source-tag duplication, or hidden restatement of an item clause. The eight steps carry the argument; every step is shorter than 2000 characters. The source locations above identify both tags and labels. citations.json contains actual substrings of the cited statements, not quotations reconstructed from their proofs.

Step 1 uses def-sbc-standard-tstructure-derived-category for an actual representative with zero terms above n. lem-pc-kflat-bounded-flat-replacement explicitly preserves that SAME bound N=n; a merely bounded-above replacement would not suffice. lem-pc-bounded-above-flat-kflat applies on the ringed space underlying S and requires only flat terms and an upper bound. def-pc-derived-pullback explicitly computes using any K-flat resolution. def-pc-derived-module-base-change-map identifies the normalized map with the appropriate pinned derived counit. These statements were opened and read. The site is the set-sized site of open subsets of S in the chosen universe.

Step 2 uses precisely the Hom bijection in lem-pc-module-pullback-adjunction. Preservation of cokernels is proved by the universal property in the step, so it is not an uncited flatness/exactness assertion and does not need a new lemma. In particular the proof never claims that a nonflat module pullback preserves kernels.

Step 3 uses the cohomology formula in def-weil-abstract-derived-category and the representative formula in def-pc-derived-pullback. The outgoing differential in degree n is zero because the actual representative has no term in degree n+1. Thus cohomology is a cokernel, which is the exact point at which step 2 applies. This checks upper vanishing even when there are infinitely many negative terms.

Step 4 checks the naturality square of the fixed counit, not an arbitrary objectwise isomorphism. The definition node specifies this counit on single modules, and the derived-category definition supplies H^0 of a quasi-isomorphism. The degree-zero right-exact cokernel map is the map induced by q^0. This proves H^0(c), including its precise normalization.

Step 5 uses the displayed standard smart truncation, the derived-category localization, and the normalized single comparison. lem-pc-pinned-pullback-counit-shifts supplies the specific shift compatibility required to identify the counit on H^n(P)[-n] with the shifted single comparison. Its statement explicitly includes the localization and termwise shift comparisons. The naturality square at the literal map p identifies the actual κ with the cokernel map already computed, so no extra comparison theorem is assumed.

Step 6 is the elementary functoriality calculation. Smart truncation preserves quasi-isomorphisms because its cohomology is the corresponding truncated cohomology; its functor and natural map therefore descend by the localization universal property stated in def-weil-abstract-derived-category. This addresses arbitrary DERIVED morphisms, not only complex maps. The other square is naturality of the one fixed counit from def-pc-derived-module-base-change-map, with the shifts supplied by lem-pc-pinned-pullback-counit-shifts. The claimed formula is just their composite. On a shifted single, the projection is identity.

Step 7 uses the full statement of lem-pc-canonical-single-pullback-square. I checked that it requires only a commutative square, not a cartesian square, and permits arbitrary N, M and a. Its four scheme maps are explicitly instantiated, its a is identity, and its ordinary comparison has inverse orientation. After the identity unit comparisons this gives exactly the composite ordinary isomorphism in the direction h^*g^*→(gh)^*. The unit laws required are stated in lem-pc-ringed-spaces-derived-pullback-composition, and the ordinary identity comparison in lem-pc-module-pullback-identity-composition. The normalized identity comparison is identity by its unit transpose under the adjunction, not by an invertibility claim about arbitrary c_g. I checked that the pinned single construction is the same counit followed by the adjunction-preserving identification. Both shift lemmas explicitly give the corresponding counit and composition shift equations; no unrelated shift is substituted.

Step 8 uses the naturality already proved in step 6 at v= c_g[-n]∘Lg^*τ_C. Its source is upper bounded by step 3; its target is a shifted single, so it also meets the hypothesis. The step spells out the equation after this substitution, then uses the single equation of step 7 and naturality of the derived composition isomorphism. The cited composition node states a NATURAL isomorphism, which is exactly what is used. This checks the order and directions in the requested formula instead of merely asserting compatibility.

I tested zero modules, empty schemes, arbitrary shifted singles, the identity morphism, a strictly smaller upper cohomological bound (H^n(C)=0), and an unbounded-below zero-differential complex. The nonflat test Spec(Z/2)→Spec(Z) with M=Z/2 has nonzero negative Tor after pullback: c is not an isomorphism in the derived category, while H^0(c) is. The proof only inverts H^0(c), so this case is covered. No properness or finite generation is used. I also traversed the statement/proof dependencies of the replacement, square and shift tools and found no path back to this item; the server checks remain authoritative.

All off-unit non-definition inputs are declared in split_report.tool_uses as generic homological algebra tools. This does not change the proper-base-change route. There is no SGA citation in this delivery's proof.

The first full dry run requested longer quotations for def-pc-derived-pullback. I replaced its short heading with the verbatim K-flat computation paragraph in each citation. This repairs the citation evidence without changing the proof.

## Unfinished work

None in this stage-1 split. The pre-existing dependencies retain their own stage status; this delivery does not claim that the entire branch is Lean-proved.

