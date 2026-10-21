# Stage-1 delivery: lem-sfb-root-tower-boundary-acyclicity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-root-tower-boundary-acyclicity.json — statement, split, no Mathlib match; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-root-coordinate-supported-vanishing.json — statement-only, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-lisse-closed-base-change.json — statement-only, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-profinite-constant-derived-functions.json — statement-only, unsplit, no Mathlib match.
- citations.json — a verbatim statement excerpt for every step/node pair.

## Attachments

None. Searched the live WeilConjectures source by the blueprint tag and root-tower/boundary/Kummer/continuous-coefficient notions. KummerCover.lean constructs punctured root covers; SixFunctors/Integral/BaseChange.lean supplies discrete small-etale integral base change, not this internal continuous-coefficient assertion. Neither is an attachment of the item or a new node. Project declarations containing sorry do not close a node.

## WANTED

WANTED: a proof of one-coordinate local-cohomology vanishing on the full prime-to-p root tower, for arbitrary affine pro-etale charts and lisse modules over all norm-continuous E and incomplete Omega coefficients, including after inverting other branches, for lem-sfb-root-coordinate-supported-vanishing.

WANTED: a proof of the specified closed derived base-change map for integral affine morphisms and lisse internal norm-continuous E and Omega modules on small pro-etale sites, with the given parameter and coefficient naturalities, for lem-sfb-integral-lisse-closed-base-change. Stacks 0EYP is its discrete-etale analogue only.

WANTED: a proof that relative profinite-test projection realizes derived internal functions of the actual all-continuous finite-dimensional coefficient model, including base change and maps over profinite families, for lem-sfb-profinite-constant-derived-functions.

## Audit and changes

The imported item has no proof and its own source explicitly asks for an exact all-continuous reference. I retained every hypothesis and conclusion. The actual source paragraph (3) of sk-thm-sf-ctf-stability-direct-images.proof.md states open direct-image preservation using sk-prop-open-coefficients. It does not state this expanded root-tower calculation. The proof is therefore marked agent, and each genuinely missing input is a statement-only node with an explicit WANTED, rather than misattributing the stronger result to a finite-coefficient theorem or to Bhatt–Scholze.

Read the current chapter record and current blueprint unit section; dag/units/sk-thm-sf-ctf-stability.json is still the older sec-six-functors unit, whereas the source of this item is the current sec-six-functors-basics expansion. This item is not the unit key and no unit record was changed. The existing created.item chain stops at lem-sfb-admissible-direct-image, so blueprint_refs.py ancestor prints None. Retained the inherited null ancestor and exact via chain, and extended it for children; each place identifies the actual current blueprint paragraph. The whole blueprint was searched for Kummer, root, acyclic, closed support, parameter, integral pushforward, profinite projection, and supported vanishing. Existing finite-coefficient strict-local Kummer nodes and root extension/support nodes were opened. None states the three proposed missing inputs. In particular lem-per-strict-local-snc-kummer-cohomology is about F_ell on a Noetherian strictly henselian regular local scheme; it does not justify all-continuous derived support vanishing.

The key fibre calculation needed care: the fibre of T over S still has nilpotent roots. It is not S as a scheme. The proof constructs the surjective closed immersion setting all roots to zero and uses the existing condensed topological-invariance equivalence, which does not require a uniform nilpotence exponent. This is a correction of a possible invalid proof inference, not a change to the item's statement.

Every new node has two phrasings and all four requested search methods, recorded directly from searches.jsonl. The semantic hits on BDeRham and Noebeling constructions do not state these sheaf results. The nearest parameter hit, LightCondensed.ihomPoints, was read in Mathlib/Condensed/Light/InternallyProjective.lean:52 onwards: it is an underived adjunction over a discrete ordinary ring on light profinite sets, with no scheme pullback or K-injective derived comparison. It is not a one-line specialization of the new node. Mathlib's integral base-change hits in Morphisms/Integral.lean:35–80 are about integral scheme morphisms themselves, not cohomological exchange. No false negative from an unavailable service was recorded; all searches used here succeeded.

## Not duplicates

lem-sfb-root-coordinate-supported-vanishing vs lem-per-strict-local-snc-kummer-cohomology: the latter computes ordinary finite F_ell etale cohomology of a Noetherian strict-local complement; the former asserts vanishing of a supported derived object on the infinite root scheme with internal all-continuous coefficients.

lem-sfb-root-coordinate-supported-vanishing vs lem-sfb-root-tower-inner-support: the latter is an outer direct-image/inner closed-unit comparison and uses the assigned item; it cannot be used to prove the item. The new input is one-coordinate local support before any direct image or nerve.

lem-sfb-profinite-constant-derived-functions vs lem-sfb-root-tower-boundary-acyclicity: the new statement involves an arbitrary affine base and a constant model with only its relative profinite test projection; it has no puncture, root construction, lisse extension across a boundary or inertia. The item's steps still perform the geometric support induction, integral exchange, nilpotent-fibre identification and normalization.

lem-sfb-integral-lisse-closed-base-change vs lem-sbc-integral-underived-exchange: existing statement is underived exchange for modules over an ordinary discrete ring on the small etale site; new statement is derived pro-etale exchange for lisse internal modules over a pulled-back norm-continuous condensed ring, with no general exactness assertion.

lem-sfb-integral-lisse-closed-base-change vs lem-sbc-integral-geometric-point-exchange: existing statement is underived small-etale exchange at one geometric point with discrete coefficients; new statement concerns the actual derived object over a closed scheme and condensed coefficients, including profinite families.

lem-sfb-integral-lisse-closed-base-change vs lem-sbc-integral-geometric-fibre-sections: existing statement identifies an ordinary geometric stalk with ordinary sections, whereas new statement is a derived module-object comparison over the entire closed scheme.

lem-sfb-integral-lisse-closed-base-change vs lem-sbc-integral-strict-local-fibre-comparison: existing statement compares small-etale sections after strict henselization with geometric-fibre sections for a discrete ring; new statement is not an ordinary section or geometric-point claim.

lem-sfb-integral-lisse-closed-base-change vs lem-sbc-integral-fibre-section-local-lift: existing statement lifts a discrete-etale fibre section to one pointed neighbourhood; it says nothing about the derived pro-etale coefficient comparison.

lem-sfb-integral-lisse-closed-base-change vs lem-sbc-integral-fibre-section-local-zero: existing statement kills a discrete-etale neighbourhood section whose fibre restriction vanishes; it is not a statement about the new derived internal-module exchange.

lem-sfb-integral-lisse-closed-base-change vs lem-sbc-geometric-fibre-exchange-germs: existing statement is a formula on pointed small-etale germs, with no integrality or isomorphism conclusion; new statement asserts invertibility of a particular derived closed exchange.

lem-sfb-integral-lisse-closed-base-change vs lem-sbc-strict-local-fibre-restriction-compatibility: existing statement identifies actual small-etale section restriction maps using strict-local legs; new statement is invertibility over a closed scheme in the continuous-coefficient derived category.

## Review by NI

I read delivery-errors B–E in full and checked these files against their mathematical failure modes. The new statements introduce their own objects and have no proof or proof_deps. Their definitions of lisse, coefficients, support and test schemes point to the exact existing definitions. The ordinary unbounded derived categories and coefficient universes are retained. I did not introduce any SGA route, any completed Omega, a finite-subextension interpretation of its functions, or an unjustified scalar/direct-image isomorphism.

For step 1 I opened the statements of the one-coordinate vanishing input, det-lem-formal-closed-support-adjunction and derived-composition-adjunction-normalization. Vanishing is supplied for every remaining coordinate after inverting the preceding ones. Each complement is a principal affine open, so the support triangle's quasi-compactness hypothesis holds even though the full root scheme need not be Noetherian. Its first term is zero and the second arrow is its actual unit. Finite induction on d=1,...,r is explicit; the composition theorem says its unit is the composite unit. Pullback and right derived direct image carry these isomorphisms to isomorphisms. The module over T[P] is pulled back from T and hence is again lisse; U[P] is an affine pro-etale base change, so the geometric input's chart hypothesis still holds.

For step 2 I read the monic-quotient-free node and finite-algebra-is-integral node, and their source calculations in algebra.tex (Tag 04GG, lemma-characterize-henselian; Tag 00GK, lemma-finite-is-integral). Their statements give the successive finite monomial bases and finite-to-integral implication used here. I corrected my initial version to cite them explicitly rather than hiding that algebra in an elementary label. The remaining filtered-colimit and nilradical arguments are written out. Every root in the closed fibre has a power equal to zero. A prime contains all such elements and the quotient is exactly the S[P] algebra, including when the base has its own nilpotents. No global nilpotence bound was inserted.

For step 3 I opened the complete statements of the integral base-change input, new-lem-weil-pbc-condensed-surjective-closed-equivalence and the derived composition normalization. The input is applied only to an integral affine morphism and a lisse degree-zero module; both hypotheses were established. The existing topological-invariance node asserts precisely that the actual condensed upperStar is an equivalence for a surjective closed immersion. Read Stacks proetale.tex Tags 09AA/09AB (lemma-closed-immersion and lemma-thickening) as its source: 09AB permits integral universally injective surjective maps, so in particular our nil closed immersion. The inverse equivalence is the specified direct image; this justifies its exactness and its degreewise derived form. I did not silently identify the nonreduced fibre with the stratum as schemes.

For step 4 I checked the full profinite-functions statement and the profinite-point-pullback composition statement. The latter explicitly includes module and derived-category pullback coherence, which is what the step uses, not a theorem asserted only in a definition's proof. S is affine, the supplied M is finite-dimensional, and its finite-dimensional norm topology is exactly the one required by the function input. This step composes actual derived isomorphisms; it does not infer a derived comparison merely from cohomology-group coincidences.

For step 5 I re-read the naturality clauses of both new comparison inputs and the normalization clause of the derived composition node. The left inverse of the open unit is gamma times lambda inverse; all units and exchanges are the specified adjunction maps. At P=* the full-fibre comparison is the canonical boundary restriction, and the pullback unit/counit triangle identities identify its inverse. Family equivariance is tested after the pro-etale base change U[Q], where it is a commuting diagram of maps over Q, using the profinite-functions input's family clause. This avoids detecting a condensed morphism solely at individual points. Ordinary E-to-Omega insertion is a map after scalar restriction; cancellation of the two natural squares proves the final square without assuming scalar extension commutes with pushforward. None of these naturalities is attributed to the mere existence of an arbitrary isomorphism.

Step 6 tests r=0, P=empty, finite P, rank zero, the empty chart and the empty stratum. The r=0 case reduces to the independent parameter-function input, and the others have zero or finite-product models as appropriate. Tested the geometric input at r=1, J=empty and after a parameter becomes invertible: empty support gives zero, while genuine support is exactly the new unsplit one-coordinate obligation. Tested integral exchange for identity and closed immersions (trivial or closed-support base change) and for the root morphism (not finite type, so its statement explicitly allows integral affine morphisms). The parameter statement at P=* has free module C_F and identity internal Hom; at empty P its free module is zero.

The three inputs are strictly distinct from clauses of the item: local support vanishing is before direct image and uses no boundary model; integral exchange is a general closed base-change comparison without a root tower; the parameter-function lemma is independent of roots and punctures. Their combination requires the full six-step argument. None depends on the item, and no circular use of root-tower-inner-support or tame-stratum descent is made. All node citations have verbatim excerpts in citations.json. Each non-elementary step is shorter than 2000 characters. I checked the larger step 5 particularly for a hidden geometric lemma; its non-formal comparison/naturality assertions are exactly clauses of the cited inputs.

## Unfinished obligations

No part of the one-level split is left unwritten. The three new inputs remain unsplit for future workers; their all-continuous assertions are not claimed proved by the present delivery. The split is an agent proof conditional on those explicit dependency nodes, as stage 1 requires. The exact references above remain wanted. No Lean was written and no compiler, Lake or build tool was run.

## Validation

Server-only preliminary review_split and check_dag invocations exited successfully. The required full deliver.py dry run and push are the final validation; their results are recorded by the delivery tool.
