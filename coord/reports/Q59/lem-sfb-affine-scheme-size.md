# Q59: lem-sfb-affine-scheme-size

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-affine-scheme-size.json: statement; split into six proof steps, no exact Mathlib match.
- citations.json: 12 verbatim statement quotations (the affine identification and quasi-compactness quotations were expanded to their full statements after the first dry-run length diagnostic), checked against the live cited node files.
- searches.jsonl: actual msearch outputs for the item, including a second phrasing.

No new nodes and no new Mathlib leaves. The finite-list and infinite-cardinal arithmetic inputs, affine principal-open geometry, and quasi-compactness are already Mathlib leaves of the DAG. Creating them again would duplicate existing nodes. No Lean was written or compiled; the repository and launcher files were read only.

## Attachments

None. Searched lean/WeilConjectures for the exact item tag and for affine scheme/cardinal/size terminology. No project declaration gives the complete size assertion. The Mathlib searches return affine covers, affine spectra and structural SizeOf declarations; those do not bound the number of affine opens and their section rings.

## WANTED

None. The source proof is present in literature/stacks-project/sets.tex, Tag 000P (lemma-bound-affine), with the size definition in section-categories-schemes. Its finite-list arithmetic is supplied by the existing Mathlib leaf, so the Kunen reference needs no new dependency.

## Corrections and route

The mathematical statement is correct and is retained, including the zero ring. Added the already existing size-definition node to stmt_deps and cited it explicitly. The imported source proof omits the localization cardinal estimate: step 4 gives the surjection A × N → A_f and the cardinal calculation. It also makes explicit the empty-cover convention and the lower bound contributed by the top affine open.

Read the latest blueprint direct-images proof, paragraph (3), and the latest unit statement, together with the chapter and stored unit records. The item is a supporting set-theoretic input below the inherited alteration/moduli/atlas branch, not a replacement for a unit step. The stored long ancestor place is historical: the latest paragraph is a compactification/direct-image assembly, rather than the earlier long proof. Kept the inherited blueprint data intact and explained the current paragraph in split_report. tools/blueprint_refs.py ancestor returns None: the inherited chain terminates at lem-sfb-admissible-direct-image, whose created.item is a Lean module name. That existing node's accepted review explicitly records this condition. Searches of the whole imported blueprint for affine scheme size and 000P found no equivalent node; same_as remains [].

## Not duplicates

No new nodes. Reused lem-weil-pbc-finite-list-cardinality rather than a new counting lemma, lem-coef-infinite-cardinal-square-power rather than a new finite-product bound, and the existing principal-open basis, affine quasi-compactness and principal-open section nodes rather than new geometric prerequisites. The scheme-size-open-cover node is a different bound and is not used, so there is no cycle with size estimates above this item.

## Review by Q59

I read the complete statement and proof of Stacks 000P in sets.tex and the preceding size definition. I also read Schemes 01HV (lemma-spec-sheaves), especially its identification of structure-sheaf sections on D(f) with A_f. For every citation below I opened the live node and used its statement, not an argument hidden in its proof. There are no new nodes requiring separate source checks.

Step 1 uses lem-weil-pbc-affine-open-spec-points, which explicitly gives the isomorphism of an affine open with the spectrum of its actual section ring. Thus it applies to the top open of Y with precisely A = Gamma(Y,O_Y). The size definition gives the lower bound from the top open and aleph_0. The correspondence of opens and sections under an isomorphism follows by composing with its inverse, so no cardinal preservation theorem is concealed here.

Step 2 uses clause (i) of lem-weil-pbc-spec-localization-away-basic-open for the principal-open basis. It uses lem-weil-pbc-affine-scheme-qcqs on U itself, which is affine by hypothesis, and def-weil-pbc-quasi-compact-scheme to extract a finite subcover. There is no Noetherian hypothesis, and no assertion that arbitrary intersections of affine opens are affine. This geometric step is marked non-elementary, and all its geometric inputs are cited.

Step 3 uses exactly the all-sets inequality of lem-weil-pbc-finite-list-cardinality. I checked Cardinal.mk_list_le_max in Mathlib/SetTheory/Cardinal/Arithmetic.lean, lines 746–750. The union map is restricted to lists with affine union before calling it surjective, avoiding the false assertion that every finite union of principal opens is affine. The empty list is included.

Step 4 uses the explicit fraction representation in def-weil-ring-localization-away, and the identity theta × theta = theta in lem-coef-infinite-cardinal-square-power. I read Cardinal.mul_eq_self at Arithmetic.lean:45. Its only relevant hypothesis is aleph_0 ≤ theta, satisfied by kappa. No domain, reducedness, nonzero f or injectivity of A → A_f is used. The finite-power calculation has its base and induction step written, so it is not an unproved additional cardinal lemma. These cardinal bounds are ordinary consequences of the two quoted statements and the definitions of cardinal comparison and products.

Step 5 uses clause (b) of lem-weil-pbc-affine-open-section-vanishing-prime, whose statement actually identifies the sections of D(f_i) with the localization, unlike the purely topological spectrum-localization node. The scheme Spec A with its top affine open meets its hypotheses. def-weil-locally-ringed-space-morphism explicitly says the structure sheaf is a sheaf of rings. The uniqueness axiom supplied by def-sc-zariski-site applies to its additive sheaf. It gives precisely the injection into the finite product, not a surjection onto arbitrary tuples. This step is marked non-elementary because it invokes the principal-open section theorem. The empty product and empty-cover sheaf axiom are spelled out.

Step 6 applies only the size definition to the bounds already proved. I checked the zero ring/empty scheme, a finite field, an infinite field, A = Z, a ring with nilpotents, f = 0, and empty affine opens. In particular Spec of a field has very few affine opens but its top section ring supplies the necessary lower bound; nilpotents and f = 0 do not interfere with the surjection from fractions. Each maximum includes aleph_0, so the finite and empty cases agree. No statement dispute or source error is needed.

Against delivery-errors B–E: no new standalone nodes or proof sketches disguised as statements; every non-elementary input has an actual cited node, all its hypotheses hold, and every quoted substring occurs verbatim. No clause is moved to a new node. The source's omitted fraction bound is written out, the product estimate includes n = 0, and the proof is acyclic at the level of the cited leaves. None of the proof steps exceeds 2000 characters; the longest is under 700. All proof dependencies equal the union of step uses. Every cited statement theorem is an existing Mathlib leaf, so there is no off-unit non-leaf tool use to request. All searches recorded for this session were run with the required command; the item's inherited NH search records are preserved.

## Unfinished

Nothing mathematical remains for this one-level split. The independent maintainer review is still required after delivery.
