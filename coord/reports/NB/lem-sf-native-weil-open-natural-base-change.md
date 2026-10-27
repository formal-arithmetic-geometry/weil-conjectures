# Stage-1 delivery: lem-sf-native-weil-open-natural-base-change

## Files written

- `dag/nodes/sec-six-functors/lem-sf-native-weil-open-natural-base-change.json`: statement, split into six proof steps; no Mathlib match for the complete native equivariant assertion.
- `citations.json`: fifteen verbatim statement excerpts, one for each step/node citation.
- No new nodes and no new Mathlib leaves. The local preparation script is auxiliary sandbox material, not a DAG delivery file.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the exact blueprint tag and for open/base-change and native equivariant operations. I read `WeilSheaf/OpenImmersion.lean`, `WeilSheaf/Operations.lean`, `WeilSheaf/UpperStarLowerStar.lean`, and the relevant declarations in `SixFunctors/ProEtale/Adic/ExtensionByZero.lean`. The open-extension construction, constructibility, and comparison with ordinary direct image do not state the required natural base-change isomorphism on the ordinary derived categories of all native Weil sheaves. No attachment is claimed from these partial results.

## WANTED

None. The proof uses the local Stacks sources and the existing categorical nodes, with no SGA route.

## What needed work

The live item had a statement and no proof. Its source Tag 03S6 describes the etale comparison and explicitly refers to the general ringed-site localization lemma. A direct citation of the finite-coefficient etale or pro-etale base-change node would not cover the native varying coefficient sheaves. I instead use the existing general ringed-site module adjunction and localization nodes, including their coefficient actions, and write the Hom chain explicitly. I also write the Frobenius morphism equation before deriving the functors; an isomorphism after forgetting Weil structure alone is insufficient.

The statement and its statement dependencies are unchanged. The live item's blueprint ancestry has `from.node: null`; `blueprint_refs.py ancestor` confirms this. Its meaningful existing `from.place` is retained. I read the current `latest` blueprint's six-operations package and the extension-zero lemma and proof in `sec-six-functors-basics/sk-prop-sf-cbc`. The current package's coefficients and the finite etale comparison are source material for the open-factor route, not an identification of coefficient categories. The generic tools from other units are declared in `split_report.tool_uses`.

## Earlier attempts and searches

The required archive-directory listing found no abandoned attempt of this item in any group. The active sandbox initially contained only dispatcher brief markers, with no node or report. The copied live item already contained four searches performed during its creation in the split of `lem-sf-native-weil-compact-base-change` by NB, timestamped 2026-10-26 at 11:17 UTC. These records remain attributed inherited evidence; I do not claim to have run those searches.

My searches are the records in this sandbox's `searches.jsonl`, at 12:16--12:17 UTC. I ran two LeanFinder phrasings, Loogle, a Mathlib grep and LeanSearch through the mandated command. Loogle and grep had zero hits; LeanFinder returned module pullback/composition, free-module, tilde and sheafification declarations, not open-extension base change on native fixed-pair derived categories. I read the pullback-composition definition in Mathlib `Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`; it does not involve extension by zero. LeanSearch was unavailable, recorded as unavailable. All five current search queries are appended exactly as logged.

## Not duplicates

No new node is created. Existing `lem-cbc-extension-zero-base-change` is an etale abelian/finite-constant-coefficient statement, `lem-cbc-proetale-extension-zero-base-change` has finite constant coefficients, and `lem-trf-open-square-exchange` likewise has finite coefficients. They do not state this native equivariant assertion. General ringed-site localization and exact derived comparison nodes are reused rather than recreated. Whole-DAG searches included Tags 03S6 and 04J0 and extension-by-zero terminology. Whole-blueprint searches used `extension by zero`, `ringed sites`, and `Frobenius equivariant`; no exact native duplicate was found.

## What remains unfinished

Nothing within this item's stage-1 split. The reused nodes retain their independent statuses; this delivery does not claim to have proved their Lean implementations. No Lean was written and no compiler or build was invoked.

## Review by NB

I read Stacks `etale-cohomology.tex`, `lemma-shriek-base-change` (03S6), including its proof by adjoints; and `sites-modules.tex`, `lemma-localize-morphism-ringed-sites` (04J0), `lemma-extension-by-zero` (03DI), and `lemma-extension-by-zero-exact` (03DJ). In particular 04J0 gives the localized structural ring map and the direct-image/restriction identity; it does not itself assert a Frobenius-equivariant derived theorem. There are no new-node sources to review.

For step 1 I opened `def-sf-native-weil-derived-framework`, `lem-weil-proetale-weakly-etale-localization`, and `lem-weil-pbc-localize-ringed-site-morphism`. The first specifies the actual native coefficient functions and operations; the second identifies open pro-etale sites with slices, not merely constant coefficients; the third permits arbitrary ring sheaves and gives identity on evaluations with the restricted ring action. I checked the restricted native ring directly on the same test object and checked that precomposition gives the localized coefficient map. The cartesian hypothesis supplies exactly the test-object fiber product needed there. No finite coefficient hypothesis is imported.

For step 2 I opened `lem-pur-site-restriction-module-adjunction-exact` and `lem-weil-pbc-ringed-topoi-module-adjunction`, as well as the localization node. They state precisely the extension/restriction and tensor-pullback/direct-image adjunctions used in all five arrows of the Hom chain. All modules lie on the stated geometric-fiber ringed sites. The construction of the isomorphism and its inverse from identities is written out: naturality of the Hom bijection proves the two inverse equations. This is a short categorical argument, not a new mathematical lemma to move below the item.

For step 3 I opened `lem-weil-pbc-mate-pasting`, including its ordinary-composition convention and both pasting formulas. I checked the four Frobenius commutation squares: all original maps are over the finite field, so geometric Galois Frobenius commutes with them. Both direct-image/restriction routes evaluate on fiber products with the same projections, and the coefficient maps precompose with their same composite projection. Pasting these equal faces and taking mates gives the displayed equation for the actual pullback and open-extension comparisons in the framework. Step 4 then uses only the framework's fixed-pair morphism definition and naturality at the isomorphism phi. It explicitly proves equivariance, and multiplying by the inverse proves equivariance of the inverse; no faithfulness assertion about a different derived fixed-pair category is used.

For step 5 I opened the complete statements of `lem-sf-native-weil-constructible-abelian`, `lem-sf-native-adic-pullback-exact-lisse`, and `lem-sf-native-weil-clopen-sheaf-comparison`. The first is exact/conservative forgetting for all locally finite-type models; the second gives exact module inverse image for every scheme morphism; the third gives exact native open extension with no quasi-compactness or constructibility restriction. Thus these cover arbitrary u, v and the two opens, including non-separated models. Exact/conservative forgetting detects zero homology of a short exact sequence, justifying the elementary exactness test for the lifted pullbacks. I deliberately do not use the more restrictive native pullback/mate statement for separated finite-type models.

For step 6 I opened `lem-sfb-exact-derived-natural-iso` and `lem-sfb-exact-derived-composition`. Both explicitly concern unbounded ordinary derived categories of abelian categories and exact additive functors; their statements contain the termwise factorization and natural isomorphism normalization used here. Thus the native sheaf isomorphism, including its inverse, descends to the required derived category. The comparison is not an identification with fixed pairs in an ordinary geometric derived category.

I tested j equal to the identity, U empty, u equal to the identity, and u with image disjoint from U. The Hom-chain comparison becomes respectively identity pullback, zero-to-zero, identity open extension, and zero-to-zero. Disconnected models and non-separated locally finite-type models require no additional argument because the proof is on localized ringed sites. Unbounded complexes cause no resolution or convergence issue since the functors are exact and the maps are degreewise. All six steps have fewer than 2000 characters. Every cited node was checked for an exact supporting statement excerpt in `citations.json`, and the relevant dependency closures do not contain this item. No statement dispute or change was necessary.
