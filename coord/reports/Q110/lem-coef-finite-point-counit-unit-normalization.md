## Files written

- dag/nodes/sec-six-functors/lem-coef-finite-point-counit-unit-normalization.json: statement, split into four steps, unchanged statement; not a Mathlib leaf.
- citations.json: one verbatim statement quotation per citation in the item's proof.
- searches.jsonl: actual msearch.py searches of the item, retained in the sandbox.

New nodes: 0. New Mathlib leaves: 0. No Lean files were written or compiled.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and the finite-point/counit, identity exceptional-inverse-image and pro-etale comparison notions. Read SixFunctors/ProEtale/ExceptionalAdjoint.lean and the relevant finite Derived/UpperShriek.lean and Derived/Comparison.lean declarations. The comparison-unit theorem supplies an input, while UpperShriek supplies the transported functor; neither states all the item's clauses, including the coefficient quotient and pinned inverse, as one finished project result. Thus no ATTACH claim is made.

## WANTED

None for this split. The existing local-field nodes already record their missing Serre reference; their statements are used as existing DAG inputs, not replaced or claimed proved here.

## Faults found and repaired

The item had an empty proof. The opening blueprint sentence says that the identity dualizing object is the coefficient unit, but it omits how the finite pro-etale transport is normalized. Using uniqueness of an arbitrary right adjoint would produce an unspecified isomorphism, so the proof explicitly substitutes the stipulated identity etale right adjoint into the finite definition and then computes the comparison counit inverse by its triangle identity. The item's statement, coefficient category and all its original blueprint metadata are retained. No statement dispute was found.

Searches of the whole DAG by constant/comparison, finite quotient and unit keywords and blueprint_refs searches for comparison unit, identity point, dualizing complex and finite quotients found the existing inputs. In particular, det-pe-classical-sheaves-unit is only about sets, so it is not used for the derived module unit. lem-pod-point-dualizing-complex states the unnormalized point result at several coefficient stages; it does not state this pinned finite-counit formula and is not cited as a substitute for the proof. The ancestor is prop-coef-integral-dualizing via lem-coef-finite-point-internal-hom-evaluation, as the existing blueprint field records.

The item's earlier Mathlib search entries have been retained. Five additional logged searches were run: two different LeanFinder phrasings, LeanSearch, Loogle for Adjunction.left_triangle_components, and grep of AlgebraicGeometry for proetale/proEtale. LeanFinder returned standard-etale algebra and unrelated adjunctions, and LeanSearch returned constant-sheaf, condensed and Gamma-Spec counits. None states the exceptional object formula. Loogle returned the defining triangle identity, read at Mathlib/CategoryTheory/Adjunction/Basic.lean:114. The local grep found the site definition and ell-adic coefficient definitions, without the required transported exceptional object. The item therefore remains a genuine split, while the triangle identity is used as an elementary defining equation, not made into a redundant node.

## Unfinished work

None for the one-level split. Existing prerequisites retain their own statuses. Delivery awaits the required server preflight and push.

## Not duplicates

No new nodes. All ingredients are existing DAG nodes.

## Review by Q110

I read the item's source, main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/lem-pod-point-dualizing-complex.proof.md, opening sentence, and the ancestor's proof in sec-smooth-purity/sk-lem-sp-tower/prop-coef-integral-dualizing.proof.md, second paragraph. This split supplies precisely the finite point normalization needed when the latter's mapping-complex adjunction is evaluated at the point. It does not change the unit or chapter route. I also read the actual source text of Stacks 099V (proetale.tex, lemma-relative-comparison), 00YV (sites.tex, proposition-functoriality-algebraic-structures-topoi) and 0H7J (sites.tex, example-constant-sheaf), together with all cited DAG statements. The proof is marked agent-written because the explicit pinned normalization is the argument written here, rather than a theorem verbatim in the blueprint.

For step 1, lem-weil-l-adic-extension-absolute-value explicitly supplies nonarchimedeanness; lem-weil-l-adic-extension-integers-dvr supplies both the DVR and finite residue field and identifies uniformizers. These verify every hypothesis of lem-weil-valued-dvr-finite-quotients. Its clause (2) explicitly says the quotient is finite; def-weil-l-adic-coefficient-extension identifies it with the chosen A. I did not treat the adjective 'finite' in a definition as the proof. The assumptions used are a prime ell, finite E/Q_ell, the actual extended valuation and n at least one.

For step 2, def-weil-pbc-site-comparison-morphism says that the comparison is a geometric morphism. The statement of lem-pe-constant-left-module-inverse-image explicitly gives the canonical isomorphism of constant ring sheaves, preserves constant scalar sections, constructs the exact module inverse image, and descends it to D+. It applies to this A without imposing a hidden flatness hypothesis. Applying it to the regular module identifies G with B after inverse image; no condensed coefficient equivalence is being assumed. I checked the rings/modules clauses against 00YV and the constant-sheaf universal property in 0H7J.

For step 3, def-amb-etale-compact-support explicitly defines the unbounded ordinary-etale candidate as Rr_* composed with Dj_!. At j=r=id its functors on complexes and their maps are literally identities. Passing a resolution through the localization gives the same object, so deriving the identity introduces no geometric theorem. The statement itself specifies the identity right adjoint: its choice needs no existence or preservation theorem here. The first finite formula of def-weil-exceptional-inverse-image is exactly nu_X^* f^times Rnu_Y,*; substitution gives omega as claimed. I checked that only this finite formula is used, rather than any downstream integral clauses of that long definition.

For step 4, thm-weil-pbc-site-comparison explicitly states the invertibility of the unit of the bounded-below adjunction for finite discrete rings and left modules, with no constructibility hypothesis. The degree-zero G is in D+ and step 1 established finiteness. Thus beta is invertible, with inverse the pullback of eta_G inverse. The stated triangle identity, also read in Mathlib Adjunction.Basic at lines 107-115, yields epsilon_B beta = 1. Composing with beta inverse proves epsilon_B = beta inverse and the other inverse equation. This is a two-line categorical computation after the cited unit theorem, and establishes the actual prescribed counit rather than an unspecified isomorphism. Both step 3 and step 4 are elementary reductions from their cited statements and definitions.

I checked edge cases n=1 (finite residue field, with no need for A to be a field when n>1), E=Q_ell (A=Z/ell^n), ramified E (no identification of varpi with ell), and nonreduced A at n>1 (the comparison theorem does not require reduced coefficients). The formula is an equality under the constant-ring and identity-functor presentations stipulated by the item, not a claim of literal equality between independently chosen derived-functor models. The triangle calculation is valid in arbitrary categories, so no unspoken scalar invertibility or degree argument enters it. Each step is below 2000 characters; the total assembly is below 3000. No hidden intermediate comparison lemma remains.

The generic DVR structure, geometric constant-module inverse image and finite derived-site comparison are recorded as tool uses in split_report with their purpose. They provide prerequisites, without replacing a step of the biduality unit. There are no new statements needing separate small-case or same-tag duplicate checks, and no SGA source is cited.
