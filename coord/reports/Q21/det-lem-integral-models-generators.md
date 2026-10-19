# det-lem-integral-models-generators — Q21 repair

## Files written

dag/nodes/sec-six-functors-basics/det-lem-integral-models-generators.json: repaired split; no Mathlib match. The statement, imported metadata, Lean record and proof steps 2–8 are retained. Only step 1, its dependency union and the worker split report change.

citations.json: 34 verbatim statement quotations covering every use in all eight steps.
searches.jsonl: actual supplementary searches; previous searches in the node are retained as inherited evidence.

## Attachments

None. Searched the read-only slopmaster2 WeilConjectures tree for the blueprint tag and integral-generator terminology, then the pro-étale six-functor tree for lisse/lattice/constructible generation. No declaration supplies all three clauses. The available adic lisseness definitions and elementary closure facts are not this theorem. No compiler or Lean file was used.

## WANTED

None.

## What was wrong and what changed

The dedicated return in coord/returns/Q21.md asks to repair the non-elementary 2641-character step 1. It included an independent support characterization and a multi-piece vanishing argument proving transitivity of extension by zero. This is exactly the generic coherence theorem already stated by lem-sfb-locally-closed-extension-coherence: its statement explicitly covers exactness, the identification with i_*u_!, and the natural isomorphism a_!b_! ≅ (ab)_!. I cite that existing node instead of copying the hidden proof to a duplicate child. The short geometric verification that a composite of locally closed immersions is locally closed remains inline. The revised step has 1568 characters; every step is below 2000. The other seven steps and their route are preserved. No statement dispute or target change is needed.

## Not duplicates

No new nodes. The candidate new transitivity lemma would be a special case of lem-sfb-locally-closed-extension-coherence, so it was not created. Whole-DAG searches for composition, locally closed extension, support and Tag 02V0 found that node. Whole-blueprint searches for “extension by zero”, “locally closed”, “support characterization extension zero” and “composite locally closed immersion” found no second blueprint statement of this item's integral-generation assertion. A support characterization alone is a two-exact-sequence argument and is not a new node either. Mathlib searches for the possible support lemma were exploratory only; their logged zero-hit greps used an incorrectly prefixed subdirectory and are not evidence of absence. The final all-Mathlib grep for the item was correctly rooted.

## Review by Q21

I read the current main-20261015 statement and all three proof paragraphs, the sk-lem-integral-models unit and its clause (4), and the fixed six-functors-basics chapter. The item retains the unit's generation, stratified-lattice, filtration and finite-descent route. I also read the relevant local Stacks passages in proetale.tex (closed immersion, exact closed image with retrocompact complement, open immersion, and the open–closed sequence: Tags 09AA, 09BM, 09BN, 09AH), and schemes.tex lemma-composition-immersion, Tag 02V0. The sources explain the generic immersion operations used by the repaired step. No prohibited SGA route is used.

For step 1 I read the complete statement of lem-sfb-locally-closed-extension-coherence, not just its proof. It states the desired exactness, factorization comparison and composition for arbitrary sheaves of rings on a Noetherian pro-étale scheme; hence it applies to the actual pulled-back condensed coefficient sheaf. sk-prop-sfb-cartesian-coefficients identifies all restrictions with the required coefficient rings. sk-def-sfb-dc-setting supplies finite type over a field; pqf-lem-locnoeth-lft supplies local Noetherianity. A field is Noetherian, finite type gives quasi-compactness, and localization/quotients give the same properties on the locally closed subschemes. def-weil-constructible-subset states the Noetherian constructibility facts. The open/closed definitions justify the elementary composition argument through two affine quotient maps. The exact ringed open–closed node supplies the factorwise exactness with quasi-compact open complements. These hypotheses hold here, so the former lengthy vanishing comparison is unnecessary. I removed det-sf-open-closed-sequence-ring-sheaf from the dependency union because its only use was in that deleted argument.

For step 2, det-lem-integral-models-operations clause (4) is the actual derived projection formula with arbitrary ambient M; it therefore permits M=E_X even though E_X need not be integral-constructible. det-prop-sfb-qlbar-colimit-x-invert-ell states both the localization identity and flatness. Cartesian coefficients give b^*E_X=E_T. This proves the scalar identity used in generation without assuming arbitrary colimit commutation.

For step 3, det-cor-coefficient-heart-ii-generation supplies finite cones of locally closed extensions of lisse sheaves. sk-lem-stratified-lattice supplies finite stratified integral lattices on the standing scheme S. det-lem-coefficient-heart-common-stratification clauses (1) and (2) give the ordered refinement and preserve lisseness. Restricting a lattice trivialization preserves finite freeness and its localization, with exact inverse image from Cartesian coefficients. No global lattice on a nonnormal scheme is presumed.

For step 4, det-lem-coefficient-heart-filtration states the finite filtration with quotients b_!(L|S_b); this is exactly the assertion used. The constructibility definition applies to a lisse finite free sheaf with its single stratum. Step 1 gives exact pushforward and transitivity; step 2 gives each integral generator. lem-sf-derived-ses-triangle supplies the triangle for each short exact sequence, while generation supplies a finite number of substitutions. The zero term is allowed by rank zero. The finite induction does not claim closure under infinite sums or retracts.

For step 5, det-lem-coefficient-finite-descent-objects states descent of the entire object to one finite E in the actual condensed coefficient categories. lem-sfb-qlbar-flat gives left exactness of scalar extension and sk-def-sfb-change-of-scalars gives its left-adjoint right exactness. lem-sf-exact-functor-derived-triangulated therefore supplies preservation of shifts and cones. The tensor associativity maps are explicitly displayed in the retained step. All resulting generators use that same E.

For step 6, the finite constant local models in sk-def-sfb-constructible include locally finite free integral modules. sk-def-sfb-bounded-constructible imposes bounded constructible cohomology and explicitly no additional derived-completeness condition. det-lem-integral-models-operations clause (3) then supplies constructibility of a_!L_0 on Noetherian X.

For step 7, det-prop-integral-criterion-constant-coefficients clause (1) identifies the finite quotient of the integral coefficient sheaf. The derived projection formula in operations clause (4), with Cartesian coefficients on S, is exactly the formula required. Local finite freeness makes tensor with L_0 a finite direct sum locally and thus flat, so the derived reduction is the degree-zero quotient; exact a_! preserves that concentration. No exactness of quotienting arbitrary integral modules is claimed.

For step 8, the ringed open–closed node gives zero restrictions off S. The constructibility definition applies on the three locally closed pieces, with zero on the two complementary pieces. def-weil-l-adic-coefficient-extension clause (4) states finiteness of A_n for n≥1, so it is discrete Noetherian. det-pe-constructible-comparison-classical requires precisely a discrete Noetherian ring, qcqs X, and a finite constructible locally closed partition with locally constant finite-type restrictions, all verified here. It gives classical origin of this same reduction, not a different coefficient category.

I checked the empty scheme, empty strata, rank zero, a closed immersion, an open immersion and the identity immersion. The coherence statement includes unitality and works for each of these. The finite-cone construction and finite reductions stay valid; n starts at 1 and includes n=1. All 34 citations are verbatim from the opened current statements in citations.json. No new statement, unsplit child, duplicate or Mathlib leaf is introduced. The generic off-unit facts (especially the newly cited immersion coherence theorem) are declared in split_report.tool_uses; they are tools for the existing route, not a replacement route.

## Unfinished work

No mathematical repair remains. The resumed validation compared the sandbox with the current repository: only proof, proof_deps, status and split_report differ; the statement and Lean record agree exactly. I read all retained searches.jsonl results before deciding no repeat search was needed. The current 34 verbatim quotations cover all 34 step/node pairs, and proof_deps is exactly their union. All eight steps are below 2000 characters (the repaired step is 1568). The first server dry run exited successfully: OK (not pushed) at 005525d432. A final dry run and push follow this report update; the terminal result records the delivered commit.
