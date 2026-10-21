# Worker report: lem-sp-subterminal-module-local-calculus

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-subterminal-module-local-calculus.json`: statement, split; nine proof steps, no new nodes, no new Mathlib leaves. The mathematical statement and original metadata/search records are preserved. Six searches actually run for this delivery are appended.
- `citations.json`: 25 entries, one for every step/node citation, quoting the cited statement verbatim.
- `report.md`: this report. `searches.jsonl` is the search command's own log; `write_split.py` is sandbox-only preparation.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and for subterminal, extension-by-zero and slice terminology did not find a declaration stating all the clauses. `CategoryTheory.site_extensionByZero_exact` in `WeilConjectures/CategoryTheory/SiteExtensionByZeroExact.lean:112` proves an abelian-sheaf extension exactness statement, under its precoverage encoding; it does not state this module-valued intersection and detection calculus. The module exactness interfaces already have their own DAG nodes and are reused through those nodes.

## WANTED

None. All sources used were available in the read clone.

## What changed and why

The item was an unsplit statement with no proof. I supplied its argument without changing any hypothesis or conclusion. In particular, the coefficient is an arbitrary ring sheaf, not a constant coefficient ring, and the derived categories are ordinary and unbounded.

The proof uses the existing general exact module adjunction, the section-normalized module-sheafification/restriction comparison, and the existing homology and triangulated-functor leaves. The singleton-summand intersection calculation, normalization of canonical maps and binary-cover detection are short arguments written in the item, not additional lemma nodes. This avoids both duplicates and nodes restating the item's clauses.

I read the chapter and unit records and the current `main-20261015` source `sk-prop-sp-tower-geometric-gluing.md`. This item supplies the module-slice prerequisites for the chart-gluing clause and unit step 5. It does not replace the tower-adjunction route or touch the unit/chapter records. No SGA source is used.

## Searches and reuse

Before choosing the dependencies I searched the entire DAG by tags 03DJ and 0F6Z and by exactness, restriction, sheafification and derived-functor terminology. I opened the actual statements of all dependencies, rather than taking their titles or proofs as interfaces. `blueprint_refs.py ancestor` identifies `det-sp-tower-gluing`; whole-blueprint searches for `subterminal`, `module sheafification`, `extension by zero` and `exact functor` found no blueprint node with the entire item statement. Its `same_as` remains the searched empty list.

I ran the prescribed `msearch.py` commands using LeanFinder (two phrasings), LeanSearch, Loogle and source grep (two patterns), and read their returned hits. All services answered. Loogle's `SheafOfModules.overFunctorMap` is transitivity of restriction, not lower-shriek intersection exchange or joint detection. I read `Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:59–87`: these constructions do not cover the full item. The semantic results concerned module-category abelianness, local generators, and scheme-specific restrictions, not the full assertion. Search texts and verdicts in the item correspond to the actual log; inherited records are retained as inherited records.

## Not duplicates

No nodes are created. In particular, `lem-pur-site-restriction-module-adjunction-exact` is reused for exactness and adjunction, `lem-weil-pbc-module-sheafification-restriction` for the section-normalized comparison, and the existing exact-functor homology and triangulated leaves for the derived clauses. The intersection and cover arguments remain steps of this item.

## Review by Q24

I read `sites-modules.tex` at 03DI (`lemma-extension-by-zero`, including the scalar action and its adjunction proof), 03DJ (`lemma-extension-by-zero-exact`) and 0F6Z (`lemma-restrict-back`). The latter is stated for abelian sheaves, so I did not cite it as a module theorem: the module-linear singleton-summand proof is written in step 3. I also read `sites.tex` at 04B8 (`lemma-almost-cocontinuous-sheafification`), `homology.tex` at 010N (`lemma-exact-functor`), and `derived.tex` at 015F (`lemma-right-derived-exact-functor`). The full continuous/cocontinuous module comparison and triangulated conclusion are supplied by the existing cited node statements; I do not attribute extra wording to those Stacks statements. There are no new-node source statements to check.

1. Step 1 applies the actual statement of `lem-pur-site-restriction-module-adjunction-exact`, which gives both functors' exactness, the sheafified presheaf construction and the natural Hom bijection for arbitrary ring sheaves. `def-weil-extension-by-zero-presheaf` explicitly supplies the direct sum, restrictions, action and singleton case; `def-weil-presheaf-modules-sheafification` supplies the linear universal property; `def-pur-localized-ringed-site` identifies slice coefficients. I checked that the theorem applies on both further slices, which remain small sites. Additivity is explained on section maps.
2. Step 2 checks continuity and cocontinuity by lifting every cover of the underlying object to the slice and comparing its pullbacks. This verifies the hypotheses of `lem-weil-pbc-module-sheafification-restriction`. Its statement explicitly includes the original unit-section formula, so the claimed normalization is available, not borrowed from its proof.
3. Step 3 evaluates on an object already over U. The singleton direct sum is the given module sheaf, and sheafifying it changes nothing by the universal property. The displayed unit is the original summand map, hence identity under this comparison. The argument applies with U and V exchanged.
4. Step 4 uses only the explicit presheaf definition and relocalization definition: the product property identifies arrows to W over U with arrows to V, and both sides use exactly the same R(C)-module and restriction map. Thus the pre-sheafification comparison really is an identity, including its zero cases. Step 2 supplies its passage through sheafification.
5. Step 5 writes both directions of the adjunction on summand sections and checks they are inverse by the cited linear universal property. This produces the units and counits actually used, rather than assuming a comparison preserves some unnamed adjunction. The self/intersection comparisons fix each section, so the compatibility diagrams agree on generators and therefore as sheaf maps.
6. Step 6 composes the displayed natural Hom bijections to identify nested extensions. Its nested-open map is explicitly the inner counit under that identification and sends the section indexed by C to A into the summand indexed by C to B. After restriction both routes fix that section, or start from zero. This gives the canonical-map compatibility without introducing a separate coherence lemma.
7. Step 7 pulls the stipulated cover back to each C and applies uniqueness in the sheaf condition from `def-weil-sheaf-of-modules-category`. It proves zero detection, as well as zero-morphism detection needed in step 8. No point or enough-points hypothesis has been added.
8. Step 8 first checks the maps compose to zero using step 7. Its cited exact-functor statement explicitly supplies kernels, images, quotients and homology preservation, so the homology sheaf restricts to zero and is zero by step 7. The abelian category exists under the original small-site hypothesis. This also checks endpoints by adjoining zero objects.
9. Step 9's cohomology comparison is exactly the statement of `lem-weil-pbc-exact-functor-complex-cohomology`; preservation of cohomology kernels/cokernels is explicitly in `lem-sp-exact-functor-preserves-homology`. This proves both directions of quasi-isomorphism detection. `lem-sf-exact-functor-derived-triangulated` is an unbounded exact-functor result, and `def-weil-abstract-derived-category` explicitly gives cohomology's localization factorization, so the derived clause uses no boundedness or injectivity hypothesis.

For section E I tested U=V=1 (all functors and comparisons are identities), U=1 and arbitrary V (the intersection comparison becomes extension from V), and disjoint covering opens (W is empty when such an object exists; the cross restrictions become zero). The formula is always sheafified before it is claimed to be a sheaf: an object not mapping to V can still admit pieces that map to V, which is why its zero presheaf value cannot be substituted for the value of the sheafified extension. I also checked the zero ring, zero module, zero maps, endpoint exactness and complexes unbounded in either direction. The proof never presumes the site has an initial object; empty-open examples are only tests on sites that have one.

Against B–E, all notions already have their definition dependencies, there are no new statement-only nodes to audit, and the proof uses no bare source tag as a substitute for a node. All 25 quoted citations were compared with their source node statements. Each proof step is under 1,000 characters, and no long step hides an extracted sublemma. The two off-unit general tools are declared in `split_report.tool_uses` with their mathematical roles. No statement dispute or correction was needed. There was no earlier attempt or return to repair; this review is the direct-delivery self-review required by the brief.

## Verification and unfinished work

The server-side `srvcheck.py ... check_dag` completed successfully: no finding introduced by the sandbox or on its nodes. Required delivery dry-run results are recorded below when available. No Lean was written and no compiler, Lake or build command was run. No mathematical part of the split remains unfinished.

The required `deliver.py Q24 lem-sp-subterminal-module-local-calculus --no-push` exited 0 and printed `OK (not pushed) ... at a7e909ef008: preflight passed`. This records the first successful dry run; the final report addition is checked once more before the push.
