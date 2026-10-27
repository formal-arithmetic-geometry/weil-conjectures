## Worker report

Files written: `dag/nodes/sec-deligne-laumon-general/lem-zl-open-compact-support-restriction-identities.json` (statement, now split; Mathlib has no exact comparison) and `citations.json`. Search history is in `searches.jsonl`.

No new nodes; no Mathlib leaves; no attachments. No WANTED literature. No Lean written or compiler invoked. No statement change, unresolved issue or discarded dependency. The item previously had no proof. Its existing statement dependencies remain necessary. The unit/chapter records are unchanged because this is a supporting lemma rather than the unit's key node.

I read the chapter and unit records, the current main-20261015 quasi-finite proof (1), and Bhatt–Scholze, Lemma 6.1.12(2), PDF printed p. 43: complementary restriction of extension by zero vanishes. The current blueprint's zero-stalk argument is realized by empty-open base change, using the completed-coefficient tools explicitly required by the item. The source's abelian/unbounded assertion alone is not treated as the entire adic normalization result.

Project searches: the exact blueprint tag has no hit in `lean/WeilConjectures`. Concept searches found `AlgebraicGeometry.ProEtale.isZero_adicUpperStar_adicOpenImmersionLowerShriek` in `SixFunctors/ProEtale/Adic/OpenImmersion.lean:216` and the related heart stalk lemma in `WeilSheaf/StalkExtensionByZero.lean`. I read these: they concern adic sheaf objects and do not state this derived comparison with its strict reductions and all three coefficient stages. Thus they are not attachments for the item. DAG and whole-blueprint searches for extension/zero, complementary restriction, completed complement and empty schemes were read; the existing completed base-change and open-reduction nodes supply the argument without a new empty-open or complementary-vanishing node. The Mathlib search commands returned ordinary ringed-space zero restrictions, algebraic adic completion, general sheaf pullback and sheafification facts; none gives the specified derived functor isomorphism. A second semantic formulation was run and its hits read. All appended searches reproduce the actual command log; pre-existing item searches were retained.

## New nodes

None. The empty-site calculation and uniqueness of maps to zero are elementary steps, not new lemmas. No clause of the item has been moved into a child.

## Not duplicates

No new nodes. Existing base-change and coefficient-comparison nodes are cited directly.

## Review by N9

I checked the split against delivery-errors B–E with the statements open. Step 1 uses the actual statement of `lem-sf-integral-open-reduction-comparison`: its r_j respects strict quotient transitions, its d_j is the displayed inverse-unit/total-limit comparison, and j_!K is complete. `lem-a1-integral-pullback-completed-comparison` explicitly gives intrinsic completeness and the normalized gamma comparison for any morphism, not merely for smooth maps or closed points. Its coefficient sheaves are exactly the completed valuation-ring sheaves here. `def-weil-l-adic-coefficient-extension` supplies finite quotients and valuation-domain data; the two-term resolution explains the perfect-quotient hypothesis rather than silently assuming flat quotients.

Step 2 uses the direct-sum formula in `def-weil-extension-by-zero-presheaf` and the universal property in `def-weil-presheaf-modules-sheafification`. It computes the presheaf on both empty and nonempty test objects. The empty covering forces the only sheaf on the empty scheme to be zero. Hence the calculation gives the actual zero functor, not merely zero geometric stalks. The pullback square is genuinely empty because the images of j and i are disjoint.

Step 3 uses the theorem statement of `lem-cbc-completed-extension-zero-comparison`, including its last sentence specifying the finite-exchange/strict-reduction construction. Quasi-compactness is an explicit item hypothesis. Step 1 supplies the intrinsic completeness required by that theorem. I reread the open-reduction and integral/completed comparison statements to check their naturality and finite-projection normalization. The displayed composition has source the actual Li^*Rj_! and target the empty extension. Its finite maps are unique zero-target maps on the already specified strict tower. The proof never asserts that finite evaluation is faithful or chooses an inverse-limit map from evaluations.

Step 4 uses the rational and common-stage constructions of the two operation definition nodes, the individual normalized compact-support scalar isomorphisms, their descent unit/associator equations, and the pullback scalar-extension theorem. Those statements really provide the source comparisons used here, with identities and composites. Once sources are identified, both composites have zero target and coincide. This proves compatibility with the prescribed comparisons without an unsupported assertion that arbitrary finite equalities lift to the integral category. These general tools are declared in split_report.tool_uses; the quasi-finite unit contains no separate coefficient-descent theorem. The chapter's route through compact-support base change is retained.

Step 5 uses the affine quotient characterization in `def-weil-closed-immersion` to justify the induced point of Z: an ideal vanishing at the kernel prime maps to zero in a field, including when Z has nilpotents. The pullback definition computes zero by zero complexes, tensors, products and the zero mapping fiber; the same remains true at rational and common stages. No assumption that the image in X is a closed point is used. No theorem about topological points alone is substituted for this scheme factorization.

I tested U empty, U=X (so Z empty), K zero, nonreduced choices of the closed complement, ramified finite coefficient extensions, repeated coefficient fields, and a geometric point over a nonclosed prime. The empty-site proof and zero-target uniqueness cover all these cases. Each step is below 2000 characters. Every dependency was read from its statement; full verbatim statement quotations accompany every step citation in citations.json. I checked that none of the cited substantive tools has a dependency path back to the item. No statement correction or source error was found.

## Validation

The server preflight dry run passed at da6fcb54a51; its durable .stage1-ready.json receipt was read after the provider interruption. The report update is rechecked before direct delivery.
