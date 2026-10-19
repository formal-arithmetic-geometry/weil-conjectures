# Q53: lem-pur-derived-support-comparison-direct-image

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-derived-support-comparison-direct-image.json`: statement, split into eight steps using only existing nodes; Mathlib has no matching supported etale/pro-etale comparison.
- `citations.json`: one verbatim statement excerpt for every step/node citation.
- `report.md`: this report. `searches.jsonl` contains the actual search-command log; `prepare.py` is sandbox-only preparation code.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched the project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the blueprint tag, support/comparison terms and K-injective preservation. The existing `AlgebraicGeometry.ProEtale.sectionsWithSupport` in `SixFunctors/ProEtale/Derived/ClosedImmersion.lean:73` defines a sheaf-valued support kernel, not the supported global sections/direct-image comparison or its compatibility clauses. The abstract derived-functor composition declarations are generic ingredients, not an attachment for this item. The archived master is reference material only.

## WANTED

None. All sources needed for the argument are present locally.

## Findings and corrections

The item had an empty proof. Its full statement is true, with no geometric finiteness or boundedness assumption beyond the stated site-size convention. I left its statement and statement dependencies unchanged. The support definition node supplies the kernel functor and bounded-below right derivation, not an unbounded theorem; Step 1 explicitly obtains the unbounded derivation from existing K-injective existence/computation nodes. I did not apply a bounded-below site-comparison theorem to an arbitrary unbounded complex. In particular no assertion that every pro-etale complex comes from the etale site is used.

The inherited `unit` is `sk-prop-a1-kummer`, while the historical blueprint ancestor is the paragraph on supported Kunneth in `lem-pur-kunneth-supported`. I retain both maintainer-owned metadata and ancestry, and declare general site/homological-algebra tools where necessary. The argument is exactly the support-comparison tool extracted by the parent, not a replacement geometric purity route. No SGA source is used.

I searched the whole DAG for K-injective right-adjoint preservation, localized restriction, etale localization, comparison pullback and support-comparison statements, and ran blueprint searches for K-injectives, comparison-pullback and support sections. Existing nodes supply every non-elementary ingredient, so no new node or duplicate is introduced. Mathlib search was executed through `msearch.py` with LeanFinder (two distinct phrasings), Loogle, LeanSearch and source grep. The returned kernel, ordinary scheme restriction, sheafification and abstract adjunction results do not state the item. Original imported search records are retained; appended records correspond exactly to the sandbox log.

## Unfinished work

None in this one-level split. Existing cited nodes retain their own states and are not edited.

## Not duplicates

No new nodes, hence no new/existing pairs.

## Review by Q53

I read the item's source, paragraph 4 of the current `main-20261015` supported-Kunneth proof, and the parent support-comparison statement/proof to identify the intended normalization. I also read the chapter and inherited unit records. The blueprint mentions support transport without giving this unbounded kernel proof, so `proof_origin.by` is `agent`. Its mathematical ingredients were checked in local Stacks: proetale.tex Section 099R (comparison is restriction), derived.tex Tags 08BJ, 070I, 070K, 070Y and 09T5, sites-cohomology.tex Section 07A5 and Tag 08FI, injectives.tex Tag 079P, sites-modules.tex Tag 04JC, and sites.tex Section 00XZ and Tag 00WX. There are no newly stated subsidiary claims to source.

For Step 1 I opened the comparison-morphism, exact-site-pullback, module-sheaf-category, K-injective-existence, support-definition and total-derived nodes. The comparison really is a geometric morphism with the specified ordinary finite-ring module adjunction. Exactness on abelian sheaves and the module definition give exactness on these module sheaves; the smallness required by the existence node is an explicit hypothesis of the item. Additivity gives the homotopy/cone calculation required for the total-derived lemma. This step explicitly handles the definition node's bounded-below scope.

For Step 2 I checked the right-adjoint-preserves-K-injective statement: its left adjoint must be exact, which Step 1 proves for this comparison. The total-derived statement computes both right derivations on these same K-injectives. The comparison-morphism statement gives actual sectionwise restriction, including the maps; the support-definition gives exactly the kernel used. Thus the displayed equality includes differentials and A-actions, not only cohomology groups.

For Step 3 I checked that the K-injective-Hom lemma concerns arbitrary source complexes and the unbounded derived category. It gives chain representatives and homotopy equivalences of K-injective representatives. The action on kernels and the restriction of a homotopy are written out using sheaf morphisms. These prove both canonicity and naturality, rather than assuming that a choice of resolution is strictly functorial.

For Step 4 I read the statements of the etale-site-localization, etale-inverse-image-restriction, weakly-etale-localization and proetale-object-inverse-image-restriction nodes. They actually identify the scheme sites/restriction functors, and the latter includes constant-ring module structures. In the etale case naturality with respect to scalar endomorphisms gives the required module version. The localized K-injective node applies to any ringed site and any object, so it imposes neither quasi-compactness nor boundedness. Evaluating the comparison on every etale object over V proves the restriction comparison needed here without a separate base-change theorem.

Step 5 is elementary after Steps 2–4: I wrote the kernel inclusion and the map s -> s|V, and checked its vanishing on U intersect V. Each square is an equality of these actual chain maps. This proves forgetting supports and open restriction, including repeated restrictions, without an unproved appeal to transport of triangles.

For Step 6 I opened the comparison-pullback and continuous-functor adjunction statements. The latter explicitly says its Hom bijection is the composite presheaf-colimit/sheafification adjunction, so its unit is the named coprojection, not an arbitrary normalization. Restricting an index W to W times_T V describes the canonical pullback comparison. For a unit section on an etale W over V, this replacement is W itself. The displayed unit equation therefore follows on the actual coprojections before sheafification and respects all scalar maps. This is a calculation with the existing constructions, not a new lemma restating the desired derived unit clause.

For Step 7 I checked the exact-functor-derived-factorization, canonical-derived-adjunction and K-injective-Hom statements. Exactness justifies termwise inverse images; Step 1 supplies existence of the right derived functors required by the adjunction theorem. The K-injective target on both sides lets the degreewise Hom adjunction compute the canonical derived Hom adjunction. I wrote the derived unit as the adjunct of the resolution map and used the very same restricted K-injective resolution, with its comparison a inverse, for the second unit. The equality follows from the preceding underived unit equation and naturality, and hence applies also to unbounded input complexes.

Step 8 checks the final-object normalization directly: the empty-cover sheaf axiom makes J(empty) zero, so the kernel becomes J(T); the cited total-derived lemma computes global sections on the same representatives. There is no unsupported use of a bounded-below Leray assertion.

I checked C=empty (zero support complex), C=T (global sections), V=empty, V=T, zero complexes and zero coefficient ring; all formulas reduce to the expected identities or zero maps. Nilpotent thickening of C has no effect because only its open complement is used. Unbounded complexes require no products, totalization convergence or cohomological-dimension bound in this proof. All steps are under 2000 characters; no long hidden lemma remains. I checked delivery-errors B–E: no new unsplit node contains a proof, every cited claim is in its statement, no clause is delegated to a restatement node, and all hypotheses of each homological/site tool are verified above. `proof_deps` is the exact union of step citations, and each citation excerpt is checked verbatim against its node's statement.
