## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-flat-scalar-direct-image-limit-coherence.json`: split into eight steps, retaining the statement and all inherited fields and searches. No new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every step citation.

## Attachments

None. I searched the current read-only `lean/WeilConjectures` by the item's blueprint tag and by scalar restriction, K-injectivity, direct image and limit terms. The pro-étale `DerivedLowerStarDerivedLimit.lean` declarations preserve homotopy-limit triangles/cones; they do not state the equality of the specified scalar/strict-tower comparison maps. The étale restriction results and normalized-tower coefficient formulas also do not give every clause under the item's general small-ringed-topos hypotheses.

## Literature

No WANTED documents. I read Stacks `sites-cohomology.tex`, Tag 0A07 (`lemma-Rf-commutes-with-Rlim`), its first tower-topos-square proof, and the preceding Tag 0941 (`lemma-derived-limit-is-ok`) explanation of K-injective tower resolutions. I read `derived.tex`, Tag 08BJ (`lemma-adjoint-preserve-K-injectives`) and Tag 070I (`lemma-K-injective`). I also read the current main-20261015 blueprint proofs of `thm-cbc-complete-proetale` and `lem-cbc-completed-extension-zero-comparison`, and the chapter and unit records. The scalar coherence calculation is my explicit refinement of the ordinary square in 0A07; the proof is accordingly marked agent-written, not attributed verbatim to Stacks.

## What changed and what was wrong

The item had a statement and no proof. No statement correction or unit-route departure was needed. The essential check is equality of normalized maps, which does not follow just from the existence of isomorphisms between their endpoints or from compatibility with tower projections in a triangulated category. Steps 3–4 give ordinary chain-map identities; Steps 5–7 identify the precise derived comparisons and substitute those identities. In particular the target resolution is explicitly `j_R = (r_V j) α_I⁻¹`, with its direction recorded, so the derived-limit image of the direct-image scalar comparison really uses a common target resolution.

No additional hypotheses were introduced. Neither exactness of module direct image nor preservation of K-injectives by module direct image is assumed. Instead the existing pushforward/limit acyclicity theorem is applied to both source resolutions. Exactness of ordinary inverse limit is not asserted: it preserves K-injectives because it is right adjoint to the exact constant-tower functor.

## Searches and Mathlib verdict

All new searches were executed through the required Q107 `msearch.py` command and are present in `searches.jsonl`. I retained the item's inherited search records. The two LeanFinder phrasings, LeanSearch, Loogle and Mathlib grep found no exact match or one-line specialization. I read `SheafOfModules.restrictScalars` at `Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean:36`, which defines ordinary restriction. The generic `CategoryTheory.LocalizerMorphism.rightDerivedFunctorComparison_fac_app` at `Mathlib/CategoryTheory/Localization/DerivabilityStructure/PointwiseRightDerived.lean:80` normalizes one derived comparison but does not supply the tower acyclicity, exact scalar comparisons or their composite equality. Classical `NatTrans.rightDerived_comp` in `CategoryTheory/Abelian/RightDerived.lean` also does not state the unbounded total-derived assertion. Thus these are useful implementation ingredients, not an attachment or Mathlib leaf for this item.

I searched the whole imported blueprint using `blueprint_refs.py search` for “direct image limit”, “scalar direct” and “strict-limit”; there is no same-statement blueprint node. The existing node statements already supply every non-elementary tool used here, so no new node was warranted.

## Not duplicates

No new nodes. The item is not a duplicate of the ordinary direct-image/limit comparison: it proves compatibility of that *specified* comparison with both flat scalar/direct-image and scalar/limit identifications. The explicit projection calculation is elementary given those ordinary identities, and was kept as a proof step rather than made a new node.

## Review by Q107

I checked delivery-errors B–E against the source and each cited node's statement, not its proof. There are no new unsplit nodes to hide an argument, no new notions needing separate definitions, and no Mathlib matches requiring an unverified line number. The existing statement's definition citations and exact comparison normalizations remain intact. Sources and TeX were retained; the proof has eight short steps, all below 2000 characters. The off-unit statement tools are declared in `split_report.tool_uses`; they supply generic resolution machinery, not a replacement route for a compact-support coefficient stage.

In Step 1, I opened `lem-weil-pbc-diagram-site-realization`: its statement supplies small diagram sites and an exact module equivalence, which licenses applying the sheaf K-injective existence statement `prop-pur-kinjective-resolutions-exist` to the tower categories. I checked that `lem-weil-pbc-flat-ringed-diagram-restriction` explicitly preserves K-injective diagram complexes and is exact, for arbitrary small J. Its ring-isomorphism and flatness hypotheses are precisely in the item, and J is either the countable tower index or the terminal category. Thus the restricted source and target resolutions really are admissible; this is not inferred merely from the definition of flatness.

In Step 2, the statement of `lem-weil-tower-category-levelwise-abelian` gives kernels and cokernels levelwise. This proves exactness of the constant-tower functor directly. Its adjunction with inverse limit follows from the definition of a compatible family. I checked both hypotheses of `lem-weil-pbc-right-adjoint-preserves-kinjective` (additive adjunction and exact left adjoint), whose statement yields all four needed K-injective limits. The statement of `lem-weil-pbc-ringed-strict-tower-homotopy-limit` supplies the total-derived-limit model. I did not substitute degreewise injectivity for K-injectivity or require boundedness.

For Steps 3–4, I checked that `def-pc-sheaf-restrict-scalars` really leaves the underlying abelian sheaf unchanged, that the flat diagram lemma specifies the underlying direct-image identity, and that `lem-weil-ringed-tower-pushforward-limit-comparison` specifies the *ordinary* composite direct-image identity inducing its comparison. The beta comparison and its product version follow directly from the compatible-family universal property with componentwise scalar action. The proof then gives the two projected expressions, which agree by naturality of alpha. This spells out the coherence calculation rather than calling it “transport” or asserting triangle-map uniqueness. The second equation is ordinary naturality of beta at j.

For Step 5, I read the entire statement of `lem-weil-ringed-tower-pushforward-limit-acyclic`: it applies to any K-injective source tower and any target K-injective tower resolution of its direct image. It has no exact-pullback or exact-product hypothesis, so it applies first to I,j and then to r_UI,j_R without an extra premise. The comparison node's statement fixes the common-derived-direct-image construction. Computing it by its defining resolution maps yields the displayed formulas for c. The flat diagram lemma states the normalization of d at K-injectives, so it applies to lim I as well as I. The resolution square j_R α_I = r_V j is explicit and fixes the model for L(d^Tow).

For Step 6, I checked the resolution-normalization clause, not just the Roos-triangle assertion, in `lem-cbc-exact-product-functor-strict-limit`. Step 1 proves restriction exact and K-injective-preserving, Step 3 proves its canonical product comparison invertible, and the item assumes exact products in all four categories. Identity target resolutions are allowed even if their terms have not separately been chosen injective. Thus the normalized lambdas are exactly beta on I and J. The K-injectivity from Step 2 justifies computing RF_R(beta) without another resolution.

In Step 7 I checked both composite types: they run from r_V F_S lim I to lim r_V J. Substituting j_R and the two elementary equations in Step 4 proves equality of those chain maps. This is an actual proof of the item's equality rather than a citation of a new node restating it. Step 8 uses the precise Hom bijection and homotopy-equivalence conclusion in `lem-weil-pbc-kinjective-hom-derived`, functorial resolutions via the diagram sites, and the already stated naturality/resolution independence of c and lambda. Hence it covers actual derived strict-tower morphisms, not just evaluated sequences.

I tested identity coefficient maps (alpha and beta reduce to identities and the formula reduces to c=c), zero complexes and the zero ring (all maps are uniquely zero), and the identity geometric morphism (the comparison is the ordinary limit identity with its specified normalization). Constant and zero-transition towers are admitted without adding a Mittag–Leffler condition. Unboundedness creates no extra step, since the cited resolutions and Hom lemma are unbounded. Nonflat changes would invalidate the restricted K-injective model, which explains exactly where the item's flatness is used. No prohibited SGA source is cited.

## Unfinished work

None in this stage-1 split. The delivery awaits the maintainer's independent mathematical review.
