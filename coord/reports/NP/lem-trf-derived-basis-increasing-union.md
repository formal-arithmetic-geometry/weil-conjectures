# lem-trf-derived-basis-increasing-union — NP

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-derived-basis-increasing-union.json`: statement, split; ten proof steps, no Mathlib match. The statement and its two statement dependencies are unchanged. All inherited metadata and searches are retained; actual NP searches are appended.
- `citations.json`: a verbatim statement quotation for every node cited by every step (including elementary steps).
- `report.md`: this report. `write_split.py` is sandbox-only preparation material, not a delivered project file; `searches.jsonl` is the search tool's actual log.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter file is changed.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` for the exact item id and blueprint tag and for increasing-union derived gluing, BBD and negative self extensions. The BBD hits concern triangulated-category and t-structure results, not this item. There is no exact project declaration to attach, and no source Lean was written or compiled.

## WANTED

None. All sources used are already present in `literature/stacks-project/`.

## Source error

The statement agrees with Stacks Tag 0D6B, `cohomology-lemma-glueing-increasing-union`, specialized to a scheme and a set-sized ordinal. No statement dispute is necessary. The source proof, however, has two slips in its limit step (cohomology.tex around lines 11439–11446):

1. It invokes `lemma-solution-in-finite-case` (0D6A) for uniqueness of two solutions on the earlier ordinal cover. That lemma assumes a finite subcover, which an arbitrary limit cover need not have. The required assertion is the uniqueness mechanism of 0D68, using Hom gluing from 0D66. Step 7 uses exactly the existing `lem-trf-derived-basis-local-hom-glue` statement and verifies its hypotheses; it does not assume the increasing-union result or general BBD effectivity.
2. The text declares a comparison `sigma: K_alpha -> C` and then chooses `tau: C -> I_alpha` representing it. These have opposite directions. Step 7 instead constructs `a: C -> K_alpha`; step 8 represents this class by `t: C -> I_alpha`. Its composite with the coprojections has class `(r_beta^alpha)^{-1}`, as required.

The source also writes the last transition formula using the restricted coprojection without explicitly taking its extension-by-zero adjoint. The split keeps chain maps into restrictions and gives their extension-by-zero adjoints in step 2. This makes every strict composition equation well typed.

## Search and reuse

The whole-DAG searches found existing nodes for K-injective representatives, exact restriction, restriction preserving K-injectives, the K-injective Hom bijection, normalized extension by zero, small module colimits, stalk/colimit comparison, stalk exactness, and filtered-colimit exactness. None was recreated. I opened their statements, rather than borrowing constructions only present in their proofs.

The whole-blueprint searches were `increasing union`, `derived gluing`, `negative self`, `0D6B` (no matches), as well as broader `K-injective`, `extension by zero`, and `stalks` searches. The latter show related generic notions, not a blueprint node stating this ordinal-gluing result. The inherited nearest blueprint ancestor is `lem-trf-local-term-locality`; the inherited `from.place` and `via` are already precise and are retained. The supporting component is the increasing-union input of the BBD-descent node, step 6, on the inherited polynomial-chart relative-duality branch.

Four new item searches were run through the mandatory msearch command and read: LeanFinder for continuous ordinal derived gluing with negative self extensions; LeanSearch with the second phrasing about transfinite recursion; Loogle `"DerivedCategory", "glue"`; and grep `BBD|[Dd]erived.*[Gg]lu|[Gg]lu.*[Dd]erived|transfinite` in `Algebra/Homology`. LeanFinder returned t-structure bounds and existence of bounded representatives, LeanSearch returned ordinary topological/sheaf/space gluing, and Loogle and grep returned no hits. None states the item, even by a one-line specialization. No unavailable service was recorded as a negative answer. The earlier creator's searches remain intact, as required.

## Not duplicates

No new nodes, hence no new/existing pairs. All supporting facts are citations of existing nodes; in particular neither the stalk-colimit calculation nor one clause of the item has been relabelled as a new node.

## Review by NP

I read the statement and complete proof of 0D6B in `cohomology.tex`, together with the uniqueness and Hom-gluing discussion (0D66, 0D68) immediately preceding it. I compared the item with its BBD-descent parent and the inherited chapter/unit records. The proof stays inside that supporting component and does not alter the unit's zero-stalk trace argument. The other-unit inputs are generic tools, declared individually in `split_report.tool_uses` with their purpose.

For step 1, I read `def-pc-derived-category`, `prop-pur-kinjective-resolutions-exist`, `lem-sc-derived-open-restriction-adjunction-exact`, `lem-sc-derived-k-injective-restrict-open`, and `lem-sf-exact-functor-derived-triangulated`. They supply precisely the module derived category, K-injective representatives, exact restriction, its preservation of K-injectivity, and its termwise derived realization. I checked the small-site requirement by using the set of all opens of each given scheme. The source checks were Injectives 079P (`theorem-K-injective-embedding-grothendieck`), Cohomology 08BS (`lemma-restrict-K-injective-to-open`) and Derived Categories 015F (`lemma-right-derived-exact-functor`). None requires boundedness or quasi-coherence.

For step 2, I read `lem-weil-pbc-module-extension-by-zero-adjunction` in full, including its explicit normalized Hom formula and unit/stalk formula, and the isomorphism-on-stalks statement of `lem-weil-pbc-sets-sheaf-iso-on-stalks`. I checked Sheaves 00A7 (`lemma-j-shriek-modules`) and 007T (`lemma-points-exactness`). The unit is an isomorphism on the interior because its stalk is the stated map, not an unspecified natural isomorphism. Its inverse is module-linear. The diagram and composition formula are then the written-out adjunction calculation, which justifies marking this step elementary. In particular the transition maps are between extensions of different complexes, not applications of a lemma only about restrictions of one global sheaf.

For step 3, I read `lem-weil-pbc-kinjective-hom-derived` and 070I (`derived-lemma-K-injective`). Its assertion allows an arbitrary source complex and a K-injective target. Restriction preservation supplies that target on the smaller open. Only the immediately preceding index is chosen at a successor, and earlier maps are defined by composition. The cocycle gives the correct inverse class and associativity gives strict, rather than homotopy, composition.

For step 4, `lem-weil-pbc-module-sheaves-colimits-forgetful` really asserts existence of all small module colimits and their sheafified termwise description. I checked Sites Modules 03DA and 03DB (`lemma-abelian`, `lemma-limits-colimits`), also the ringed-space version Modules 01AH (`lemma-limits-colimits`). The ordinal segment is a set, so the smallness hypothesis holds. The differential, the coprojections and their equations come directly from the universal property; no inverse limit, homotopy limit or general descent assertion is being substituted.

For step 5, I checked `lem-weil-pbc-module-stalk-filtered-colimit` for the actual coprojection comparison, the normalized interior stalk formula of `lem-weil-pbc-module-extension-by-zero-adjunction`, and `lem-weil-pbc-module-stalk-exact` for kernels and images. The relevant sources are Sheaves 009E (`section-limits-sheaves`), Modules 01AH and 01AG (`lemma-abelian`), and Sheaves 00A7. The point lies in the chosen earlier open; therefore the whole tail lies in the interior and has the specified stalks. I wrote the universal-property proof that discarding earlier indices does not change this colimit. I do not require stalks to commute with an inverse limit.

For step 6, the exact-colimit statement used is exactly `lem-weil-pbc-filtered-colimit-abelian-groups-exact`, checked against Algebra 00DB (`lemma-directed-colimit-exact`). Together with the stated kernel/image stalk identities this gives the cohomology calculation. I wrote the cycle/boundary verification and the inverse construction for the cohomology-colimit map, rather than citing an uncited theorem about homotopy colimits. This is an elementary consequence of the cited exactness result. Exactness detection on every stalk makes the kernel and cokernel of each cohomology map zero, hence gives a quasi-isomorphism.

For step 7, I opened `lem-trf-derived-basis-local-hom-glue`. Its statement gives a Hom bijection for global objects over an intersection-refining cover; it is not merely fully faithful Yoneda, uniqueness without Hom, or a definition. On the limit open the earlier nested opens cover by continuity, their intersections are members, and both restricted global objects are isomorphic to the same K_beta. Thus the required cross negative Hom groups vanish. I checked the displayed cancellation proving compatibility of the local maps and repeated it for their inverses. The Hom injectivity then proves the two inverse identities. Duplicate opens give equal local maps by that same cancellation, so passing from ordinal indices to a set of opens is harmless. This corrects both slips identified above.

For step 8, 070I is applied with the K-injective target I_alpha itself and arbitrary source C_alpha. I checked the direction `C_alpha -> K_alpha`, the resulting inverse class, and the exact chain-map composition calculation. This completes the induction before the final object is constructed.

For step 9, I checked again the statements for existence of module colimits, stalk/colimit comparison, normalized extension stalks, exact filtered colimits and stalk exactness. This repeats the explicit calculation of steps 5–6 for the final diagram and a nonempty filtered tail. It needs no continuity assumption at lambda, which need not belong to the indexing family. Step 10 inverts the coprojection equation; its resulting order of composition is exactly the conclusion in the original item.

I tested lambda = 0 (the cover forces the empty scheme), lambda = 1 (W_0 is empty), successor lambda with a largest index, a genuine limit cover with no finite subcover, all zero complexes, repeated opens and repeated opens with nonidentity transition automorphisms. The base and cocycle equations cover all these cases. No finite subcover, separatedness, finite cohomological dimension, boundedness, or quasi-coherence is used. Negative self Hom vanishing is used exactly where it is needed, to glue the limit comparison in step 7.

All ten steps are shorter than 2000 characters. I reviewed them individually for hidden comparison lemmas: the extension diagram equations, cohomology-colimit calculation and comparison cancellations are explicitly written; each non-elementary input is the statement of a cited existing node. The JSON is single-escaped TeX, new unsplit nodes do not exist, proof_deps is exactly the union of step uses, and citations.json quotations are literal substrings of the statements read. No SGA source or alternative purity route is used.

## What could not be finished

None. The split and self-review are complete; the required server dry run and delivery are the remaining gates.
