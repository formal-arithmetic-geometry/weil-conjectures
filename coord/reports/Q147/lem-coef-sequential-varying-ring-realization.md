# Worker report: lem-coef-sequential-varying-ring-realization

## Files written

- `dag/nodes/sec-six-functors/lem-coef-sequential-varying-ring-realization.json`: statement; status split; seven proof steps using existing nodes. No new nodes and no new Mathlib leaves.
- `citations.json`: verbatim statement quotes for all 19 step/node citations.
- `report.md`: this report. `searches.jsonl` is the unmodified output log written by msearch.py.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the exact item id and the blueprint tag, sequential realization, and varying-ring terminology. There is no declaration of the project stating all clauses. References to varying coefficient sheaves in upper/lower-star modules concern different operations, and the filtered-colimit varying-ring statements are not this inverse-sequence realization.

## WANTED

None. The sources needed here are available locally.

## Corrections and scope

The imported item had no proof. Its mathematical statement is retained, including arbitrary unbounded complexes, arbitrary compatible coefficient sheaves, all composite transitions, and retention of any prescribed first representative. I corrected only typography: doubled TeX backslashes and literal paragraph-newline escapes in the imported statement. There is no mathematical statement dispute and no added hypothesis.

The nearest blueprint ancestor is `lem-coef-integral-compact-support`, paragraph 2, the coefficient maps making a normalized tower before effectivity is applied. I read the main-20261015 proof, its parent normalized-realization split, the item unit and chapter records, and the three-level rules. The blueprint does not spell out the recursive chain realization. This proof is therefore marked agent-written. It makes that prerequisite explicit without changing the compact-support, coefficient, purity, or effectivity route. No SGA source is used.

The existing `lem-pc-right-fraction-representation` has a minor source-label mismatch: its Tag 04VI is correct, but the local Stacks label is `lemma-morphisms-right-localization`, not its recorded `lemma-right-localization-finite-diagram`. I use the actual 04VI statement (a singleton finite collection of arrows), and do not edit the other node.

## Searches and reuse

I searched the whole DAG for Tag 05RT, calculus of fractions, roofs, strictification, chain representatives, scalar restriction and tower evaluation; then opened the statements of the candidates used. Blueprint searches included `calculus of fractions`, `sequential realization`, `inverse sequence`, `strict inverse`, `restriction of scalars`, and `realization`. No imported blueprint node states this simultaneous realization. The item already had `same_as: []` and a precise `from.place`; those remain valid.

The crucial facts already exist as `lem-pc-quasi-isomorphisms-multiplicative-system` and `lem-pc-right-fraction-representation`, both Mathlib leaves. Tower abelianness and exact evaluation are already `lem-weil-tower-category-levelwise-abelian`. Exact scalar restriction and its cochain-compatible derived compositors also have existing nodes. Thus I create no roof-lifting, sequence-assembly, or complex-of-towers node: the actual induction and the two indexwise constructions are steps of this item.

I ran five fresh msearch.py queries, using leanfinder twice, loogle, grep and leansearch; their exact queries and results are appended to mathlib_searches and recorded by the search command in searches.jsonl. I retained the five inherited search records. The returned object/arrow essential-surjectivity facts were read in DerivedCategory/Basic.lean (Qh.mapArrow at 181, Qh at 192, Q at 195); they do not retain fixed targets simultaneously over varying coefficient rings. Bounded roof factorizations and the mkHom/InductionUp constructions likewise do not state this theorem. These results support reuse of general fraction lemmas, not an attachment or a Mathlib-leaf claim for the item.

## Not duplicates

No new nodes were created. In particular, I reused the existing general right-fraction theorem instead of introducing its special case for module sheaves. The nearby `lem-pe-kflat-scalar-tower-realization` concerns the reduction tower of one K-flat complex with specified tensor-adjunction units; it does not realize arbitrary M_n and tau. `lem-coef-derived-system-evaluation-calculus` begins with actual derived systems and studies adjunctions and Hom, not lifting an arbitrary sequence with a prescribed C_1.

## Review by Q147

I reviewed sections B through E of delivery-errors against the node, the cited statements, and the sources, rather than relying on the imported proof or on tags alone. I read Stacks derived.tex Tag 05RT (`lemma-acyclic`) and Definition 05RU, categories.tex Tag 04VI (`lemma-morphisms-right-localization`), sites-modules.tex's ordinary restriction construction and Tag 03DA (`lemma-abelian`), derived.tex Tag 015F (`lemma-right-derived-exact-functor`), and homology.tex Tag 02MZ (`lemma-inverse-systems-abelian`). There are no new-node sources to review. The derived comparisons used are stated by the cited exact-factorization and exact-restriction-composition nodes themselves; no construction is borrowed only from a cited proof.

Step 1 uses the actual abelian-category clause of def-weil-sheaf-of-modules-category and the actual same-underlying-sheaf restriction definition. The exactness clause of lem-pur-sheaf-ring-coefficient-ordinary-adjunction explicitly preserves both finite limits and finite colimits. The sheafification and size hypotheses hold on the specified small site in the compatible larger module universe. No flatness, quotient, finite, or nonzero-ring hypothesis is used. Lem-weil-pbc-exact-functor-derived-factorization gives termwise unbounded derived functors, with natural cochain comparisons. Lem-pur-exact-restriction-composition gives precisely the cochain-compatible composition comparisons. I wrote the section actions to verify that their ordinary comparison is the intended identity-on-underlying-sheaves map, rather than simply asserting transport.

Step 2 uses the localization model in def-weil-abstract-derived-category: objects are represented by complexes. The supplied first pair is used literally. I stated the induction invariant and its vacuous arrow condition at n=1, so the fixed-first-pair clause is part of the argument.

Step 3 uses lem-pc-quasi-isomorphisms-multiplicative-system in K(Mod(B_{n+1})), where the category is abelian by Step 1. Lem-pc-right-fraction-representation applies to the displayed g between the indicated localized objects; it supplies both an S-denominator into the new source A and a numerator into the already fixed restricted target C_n. Its statement does not promise fixed-target chain maps directly: I explicitly pass from homotopy-class arrows to representative chain maps by the definition of the homotopy category, and set i_{n+1}=aQ(s). The equality verifying the invariant is written out. This never replaces C_n or any previous map. Recursive choice is over the positive integers, within the fixed containing universe; there is no uncontrolled large indexing category. No K-injectivity or K-flatness is assumed or needed.

Step 4 uses only the restriction definition and its cochain-compatible compositor, together with the established adjacent equations and the hypothesis tau_{r,n}=Res_{r,m}(tau_{m,n})tau_{r,m}. I wrote the induction on m-n, including its identity case and all intermediate equations. This proves the composite clause rather than moving it into a node that restates it.

Step 5 uses the definition of scalar restriction and only the first, general definition of Tow_B(T) in def-weil-pbc-adic-coefficient-datum. I am not importing that node's later Noetherian adic datum or finite quotient assumptions. The section formula verifies R-linearity using q_{m,n}pi_m=pi_n, and the identity/composition equations give the functor on the poset. This is a direct construction, not a strictification theorem being silently assumed.

Step 6 uses that same strict-tower definition and the cochain-complex definition in def-weil-abstract-derived-category. The displayed square is the chain-map equation for the u_{m,n}; its componentwise square-zero equation proves that the differentials define a complex in the tower category. No assertion about evaluation on homology is substituted for this actual complex.

Step 7 uses the entire exact-evaluation clause of lem-weil-tower-category-levelwise-abelian, with A=Mod(R), and the termwise factorization of lem-weil-pbc-exact-functor-derived-factorization. Its comparison is a derived isomorphism, not a degreewise statement. I explain how the natural strict transition descends: its naturality with inverted arrows implies naturality with their inverses. Applying the cochain-compatible restriction comparison and Step 4 then gives the exact stated transition, including the restricted i_m and i_n. No joint faithfulness on derived Hom groups is claimed or used.

All uses entries have quotations copied verbatim from the corresponding node statements in citations.json. All proof_deps are exactly the union of those uses. The off-unit statement citations are Mathlib leaves or generic exact-scalar tools in sk-def-sf-operations, which the item's unit already cites; there is no route replacement and no extra tool-use approval is required.

I tested the induction on a single level (it retains arbitrary C_1), two levels (the first right fraction has the asserted domain and fixed target), and three levels (the explicit cocycle equation gives tau_{3,1}). Equal indices yield identities. Zero transitions may be represented by zero numerators, without changing prior complexes. Zero objects and zero coefficient rings cause no failure. Identity coefficient maps recover the ordinary sequence construction. Unbounded cochain complexes remain unbounded throughout, and no bounded factorization lemma from the search hits is applied. Non-surjective and non-flat ring maps cause no problem because only exact restriction is used. On an empty site the trivial module categories satisfy the same construction. Every proof step has fewer than 2000 characters, and none hides an additional non-elementary lemma beyond the nodes cited.

## Unfinished work

None in the one-level stage-1 split. No Lean was written or compiled, and no library proof is claimed. Delivery awaits the required server dry run and push.
