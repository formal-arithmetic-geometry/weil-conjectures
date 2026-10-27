# Stage-1 delivery: lem-sf-open-quotient-completion-unit-comparison

## Files written

- dag/nodes/sec-six-functors/lem-sf-open-quotient-completion-unit-comparison.json: statement, now split in seven steps; no statement change. Mathlib searches found ordinary completion, ordinary pullback and condensed-module interfaces, not this assertion.
- citations.json: 25 verbatim statement quotations, one for every step/node citation.
- report.md: this report. searches.jsonl is the search tool's own log.

No new nodes; no new Mathlib leaves. The sandbox was empty of a node and report when this attempt began. The item's pre-existing searches and metadata are retained, with this attempt's actual logged searches appended.

## Attachments

None. Searches under lean/WeilConjectures for the exact blueprint tag and for quotient/completion-unit, strict tower and Roos terminology found no declaration covering the whole item. Reduction.lean's isIso_reductionModIdeal_map_completionAdjunction_unit_app concerns reduction of a completion-adjunction unit, not the strict open quotient isomorphism and all its normalization equations. The generic normalized-tower modules do not state the open restriction comparison. None is claimed as an attachment.

## WANTED

None. The source route and generic interfaces are available in the local literature.

## Problems and corrections

The item was statement-only, not a completed split. The statement was retained. I filled its proof with the actual strict tensor and augmentation argument and verified all hypotheses of the exact-product comparison. No unit or chapter route was changed. The proof is marked agent-written: Stacks 099N proves the ordinary-pullback/finite-reduction route, but does not itself state this entire completed-ring, strict-tower, signed-Roos normalization. The original generic exact-product theorem already explicitly supplies the normalization and augmentation compatibility needed here.

I avoided two invalid shortcuts: an isomorphism of inverse systems in a derived category does not by itself supply an isomorphism in the derived category of strict towers; and agreement of the projections of maps into a derived limit does not by itself identify the maps. Step 4 descends strictly commuting maps from good representatives, and Step 6 uses the zero shifted-product component in the normalized Roos model.

The initial Loogle query `SheafOfModules, PreservesLimits` was rejected for an unknown identifier; that diagnostic is recorded, not treated as evidence of absence. The corrected ordinary pullback query produced relevant interfaces but no exact match. Both semantic phrasings and the grep were actually run through msearch.py and their returned hits read. No searches were invented. Earlier recorded searches belonging to the imported item were preserved.

## Unfinished work

None for this one-level split. The cited existing nodes carry the remaining generic mathematical dependencies; no new statement-only obligations were needed.

## Not duplicates

No new-node/existing-node pairs: no new nodes were created. Whole-DAG and blueprint searches for K-flat/tensor inputs, completion unit and strict quotient found existing interfaces; they were reused. In particular the item is not replaced by a newly named clause of itself.

## Review by Q146

I read coord/delivery-errors.md sections B through E in full, the item's statement and metadata, its unit sk-prop-sf-pf-coherence and chapter, and the current main-20261015 prop-sf-pf-coherence proof's open-factor base-change paragraph. I followed that route. For the item's mathematical source I read Stacks proetale.tex, Tag 099N (lemma-pushforward-Noetherian-case), its clauses (2),(5) and proof of (5); sites-cohomology.tex Tags 0G7E (lemma-pullback-K-flat) and 07A4 (lemma-pullback-tensor-product); and sites-modules.tex Tag 03EL (lemma-tensor-product-pullback). I also read the local blueprint proof of det-pe-products-exact and the completed-extension-zero proof paragraph underlying the existing exact-product strict-limit interface. There are no new nodes with separate sources to review.

For Step 1 I opened the full statements of lem-weil-proetale-weakly-etale-localization, lem-weil-pbc-profinite-coefficient-inverse-image, lem-pc-kflat-resolution, lem-pur-site-restriction-module-adjunction-exact, lem-weil-pbc-ringed-topos-kflat-pullback and lem-pur-derived-change-of-rings. These respectively give the slice-site identification, the finite/limit projection and transition normalization, an unbounded flat-term K-flat representative, exact restriction, preservation of that good representative class and computation of derived quotient scalar extension. The ring map in the K-flat theorem is the identified restriction of B_W; its hypotheses hold for this ringed slice, not for an incorrectly assumed constant ring. The finite quotient maps are unital and the coefficient datum says their rings are finite, as required for the coefficient-identification theorem.

For Step 2 the full statement of lem-pur-independent-inverse-image-tensor-comparison explicitly gives the pure-tensor normalization, not merely an unspecified derived isomorphism. I combine it with the coefficient compatibility statement and def-pc-tensor-complex-sheaves, whose differential on tensor with a degree-zero ring is d_P tensor 1. The projection normalization checks linearity over B_V after restriction of scalars. No assertion that a non-flat quotient is flat over B is used.

For Step 3 def-weil-integral-reduction-tower actually states the strict gamma_n and tau_n formulas, while def-pur-sheaf-tensor-product defines the sheafified tensor. The transition and augmentation squares are checked directly on local tensors; both sides are written in the step. This is the only elementary step. It introduces no new lemma or unproved compatibility.

For Step 4 I read lem-weil-pbc-site-derived-tensor-descent, which states the equivalence from the localization of flat-term K-flat representatives, not just a fully faithful Yoneda fact. lem-pur-derived-change-of-rings states that a quasi-isomorphism between K-flat complexes remains one after change of rings. lem-weil-tower-category-levelwise-abelian gives the actual levelwise kernels and cokernels, so their cohomology and quasi-isomorphisms are levelwise. Exact restriction is provided by the cited adjunction lemma. Together these make quotienting and restricting genuine functors out of the representative localization, with strict maps and their homotopies before localization; the resulting comparison is independent of the chosen representative. I did not cite lem-weil-integral-reduction-tower-well-defined for this stronger conclusion: its statement is only an isomorphism of systems in a derived category.

For Step 5 det-pe-products-exact states exact products for every sheaf of rings on a small pro-etale site, hence for both completed coefficient sheaves, with no Noetherian or quasi-compact hypothesis on the schemes. The extension-by-zero left adjoint in lem-pur-site-restriction-module-adjunction-exact supplies the explicit Hom calculation establishing preservation of products by restriction. The normalized comparison and its augmentation clause are exactly the statement of lem-cbc-exact-product-functor-strict-limit; I verified its exactness, additivity, canonical product-isomorphism and countable exact-product assumptions here. The signed Roos differential and theta/kappa normalization are the ones in that cited statement.

For Step 6 lem-weil-pbc-ringed-strict-tower-homotopy-limit supplies the functor Rlim on the derived category of strict towers. lem-weil-strict-roos-comparison explicitly identifies ((gamma_n),0) with the canonical augmented derived map and gives naturality for strictly commuting squares. This is sufficient to identify the actual map, not just its component projections. Applying tau to those coordinates proves b alpha = eta, and the previous step gives the other equation; their composition gives rho e*eta = eta.

For Step 7 I opened def-weil-pbc-completed-pullback. Its statement constructs the comparison by applying the total left derived strict-tower pullback to the quotient augmentation and composing with the constant-tower derived-limit unit. By the cited levelwise abelian and exact restriction statements this particular pullback is exact on strict towers. lem-sf-exact-functor-derived-triangulated identifies its termwise derived localization. Thus the definition's augmented construction is the one defining alpha, using the canonical exact-localization identifications. The normalized strict Roos statement identifies its unit construction with the augmented map. I only identify the completed functor on complete inputs, where that definition defines it; the augmented construction and equations themselves use arbitrary H.

I checked small and boundary cases: for e the identity all coefficient and tensor comparisons are identities and the equations reduce to the same quotient augmentation; for the empty open all complexes and maps in the target are zero; H=0 gives the zero strict tower; n=1 uses the same unital quotient formula and requires no inverse of t. For unbounded H, only unbounded K-flat and total strict-limit results are used, and for a non-quasi-compact open the slice adjunction and product argument still apply. No extra completeness, constructibility, boundedness, flatness of A_n over B, or quasi-compactness was introduced. All seven non-elementary/elementary step flags have been considered individually, and every step is below 2000 characters. I checked the citations against the opened statements and generated citations.json by exact substring verification. Off-unit generic tools are declared in split_report.tool_uses; they do not replace the unit's open-factor route.
