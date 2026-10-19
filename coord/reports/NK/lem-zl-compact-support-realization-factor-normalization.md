# Worker report

Item: lem-zl-compact-support-realization-factor-normalization. Group NK. Stage 1, direct delivery, 2026-10-18.

## Files written

- dag/nodes/sec-zeta-weil/lem-zl-compact-support-realization-factor-normalization.json: existing statement node, split into nine steps. Statement unchanged. No Mathlib match.
- No new nodes, Mathlib leaves, Lean files or unit records.
- citations.json records every step/node pair, with a verbatim excerpt of the cited statement. searches.jsonl is the search command's original log. The two local preparation scripts only write this sandbox.

## Attachments

None. Searched WeilConjectures in /home/ubuntu/weil-src-slopmaster2 by the blueprint tag, factor normalization, compact-support realization and adic/condensed realization terminology. The closest adic result, isHomotopyLimit_mapCone_rightDerivedLowerShriek in SixFunctors/ProEtale/TraceFormula/Adic.lean:261, contains sorry and concerns compact cohomology, not these specified comparison maps. It does not attach this item. The exact upstream master definition boundedConstructibleLowerShriekOfCompactification in ModuleObject/Derived/BoundedConstructible.lean:268 is the proper/open composite; its surrounding constructibility obligations are sorried, and it does not prove either normalization equality.

## WANTED

None. The necessary sources and supporting DAG statements are present.

## Audit findings and changes

The item arrived unsplit, with no proof and no local earlier attempt. Retained its statement, blueprint ancestry, creation record, original source qualifications and all previous searches. Added actual Mathlib searches under NK, preserving the exact query text and reading the returned signatures. Loogle gives ordinary sheaf adjunctions; LeanSearch gives ModuleCat scalar-extension adjunctions; the two LeanFinder phrasings give ordinary sheaf and discrete/solid condensed adjunctions. Grep gives unrelated compactness, polynomial and counit documentation. None supplies the integral reduction/limit normalization and both compact-support comparisons. No declaration or leaf was fabricated.

The key distinction is between isomorphism detection and equality detection. Step 1 only uses derived evaluation to detect an isomorphism. Steps 2–4 establish equality using actual system adjunctions, generator squares and the bridge. Steps 5, 6 and 8 expand the defining specification of a and xi from lem-pur-compact-support-condensed-realization, rather than treating an arbitrary isomorphism between the same functors as that specification. In particular that node's construction Steps 3–6 and 13 explicitly define the named arrows that its statement specifies; they are read to unfold those arrows, not used as an unstated auxiliary theorem or as an object chosen from another node's proof.

No statement dispute or correction was needed. The source is already correctly qualified as agent formulated: Bhatt–Scholze supplies context, not the displayed equality. The current main-20261015 rationality unit is more general than the archived unit JSON (finite type instead of smooth proper geometrically connected); this item is a supporting coefficient tool, not its key statement, so no unit record or route was altered.

## Not duplicates

No new nodes. Searched the entire DAG and blueprint for compact support realization, coefficient projection and open tensor. The existing generator, open comparison, semilinear section, coefficient presentation, finite-free direct-image and continuity nodes give the smaller ingredients. The same-tag and elementary-node issues therefore produce no new nodes. The item is not replaced by a new node restating a clause.

## Review by NK

I read Bhatt–Scholze Definition 6.7.6 (compactification definition), Lemma 6.7.14 (coefficient context), Proposition 6.8.14(2) (rationalization equivalence) and Remark 6.8.15 (actual ambient functors), and compared the proper/open composite with the master definition at line 268. I read main-20261015 fix-prop-coherence.proof.md and the current rationality unit. I also read the local Stacks statements and proofs for 0GL1, label lemma-j-shriek-and-tensor; 0E47, label remark-compose-base-change-horizontal; and 0A07, label lemma-Rf-commutes-with-Rlim, in sites-cohomology.tex. The first two omit details and do not alone prove this item's normalization. The delivery uses the existing stronger DAG statements for those obligations. No SGA source is used.

Step 1 uses the statements of lem-weil-pbc-profinite-coefficient-inverse-image (coefficient maps and quotient compatibility), prop-weil-pbc-direct-image-limits (the specified diagram-site projection mate and finite perfect quotient isomorphisms), lem-sf-integral-open-reduction-comparison (the actual strict r_j), lem-coef-semilinear-derived-sections (evaluation detects isomorphisms), lem-weil-compact-support-reduction-tower-functor (the actual functor and transitions), and lem-weil-pbc-constant-completion-equivalence (identification of the actual completion units). def-weil-l-adic-coefficient-extension supplies the DVR and finite quotients. The two-term finite free resolution proves perfection; no flatness of quotient ring maps is claimed. Completeness of the open and proper intermediates, compatible origins, and common bounds are the item's explicit hypotheses.

Step 2 uses the basic formula r_A=e R(d_A inverse) in lem-sf-generator-reduction-coherence and the unit/counit equations in lem-coef-derived-system-evaluation-calculus. I checked the types: d_g starts at L S_g r_Z(j_!K), and L S_g(r_j inverse) starts at P_RK. Their composite therefore has target P_R^0K. The calculation is elementary after those cited statements. Its other equation e_N r(q)=b is naturality plus the left triangle, not an evaluated equality.

Step 3 uses the *statement's* generator square of lem-sf-generator-reduction-coherence, including proper/open interchange and its integral counterpart. Applying L and the actual unit gives the displayed conjugation formula in two lines. The open comparison statement fixes d_j and its units/counits; lem-sf-integral-compactification-system-realization explicitly covers arbitrary expression contexts and whiskering. I did not infer that stronger assertion from finite-level maps.

Step 4 uses the *displayed equality in the statement* of lem-sf-integral-compactification-comparison-bridge, retaining its direct d_v identifications, compatible tower and inserted counit. I corrected an earlier draft which only said these coordinates agreed: the delivered step explicitly writes Q_{g,f}, expands the two q's, and cancels e r(u). The bridge formula and the generator squares then give the specified completed-composition equality. All intermediate objects remain within the hypotheses required by the bridge; this assertion is made when its supplied compatible tower is present, not for an arbitrary diagram without that data.

Step 5 unfolds the specification of a, then uses the statement of lem-weil-pbc-condensed-e-realization for the actual direct-image comparison and its adjunction compatibility, and lem-sf-open-tensor-normalization for the open-unit adjunct. Since J is scalar extension, these are the same factors. Associating this prescribed composite is elementary. It makes no assertion that the mere existence of an isomorphism in the parent's statement would determine its normalization.

Step 6 uses finite freeness from lem-weil-pbc-condensed-flat-coefficient-calculus and the exact counit-transpose formula and invertibility in lem-sp-finite-free-direct-image-coherence. The coefficient inverse-image maps are the composition maps of def-weil-pbc-condensed-e-module-category, so the finite-free theorem's square of coefficient maps commutes. The open factor is exactly the identity-on-the-open comparison of lem-sf-open-tensor-normalization. Expanding the canonical composite coefficient projection defining xi gives its stated factorization. Invertibility holds already in the F-module derived category.

Step 7 uses prop-weil-pbc-qbar-condensed-two-colimit only for the actual coefficient ring and finite-stage cocone, not for an unasserted faithfulness of finite evaluation. The statement of lem-weil-pbc-condensed-coefficient-complex-presentation supplies a simultaneous bounded-below representative and the transposed cocone maps. lem-weil-pbc-condensed-flat-coefficient-calculus gives exact scalar extension and its tensor-colimit comparison. The input j_!K_E is bounded below and all finite scalar extensions keep that bound; proper g is qcqs, as required by lem-weil-pbc-condensed-qcqs-pushforward-continuity. The statement of lem-weil-pbc-ring-sheaf-change-adjunction supplies the derived restriction/direct-image comparison, preserves the relevant adjunction and reflects isomorphisms. The cocone-leg transposition identifies the resulting map with the actual Omega-linear counit mate. No use is made of the full continuous-function sheaf C(-,Omega).

Step 8 uses the open statement for the ring change E to Omega directly. The proper coefficient cocycle is precisely the equality in lem-pur-ringed-coefficient-projection-cocycle; the open equality is its explicit identity-under-restriction adjunct calculation. The presentation theorem controls the cocone arrows. This shows that the colimit construction specifying xi is the same ordered proper/open composite in the Omega-module category.

Step 9 checks naturality of the written factors and the identity and empty cases. For j=id, the open unit and both open comparisons are identity. Then q inverse is d_g, not an arbitrary automorphism. If g is also identity, q is the completion unit, not literally the identity before reconstruction coordinates are identified. Zero input and empty open give zero objects. F=E gives the identity coefficient projection by the cocycle's statement. These checks rule out an accidentally omitted nonempty or nonzero hypothesis.

I checked B–E of delivery-errors.md against these files: no new self-containedness or Mathlib-leaf obligations arise; all cited statements were opened; every non-elementary input is a cited node; proof_deps is the union of uses; no definitions are substituted for missing theorems. Structural comparison lemmas from other units are declared as generic tools in split_report.tool_uses, since the rationality unit does not itself develop the coefficient calculus. Every step is below 2000 characters; the longer finite-subfield step is an application of existing presentation, continuity and restriction-adjunction statements, not a hidden new comparison lemma. citations.json covers all 36 step/node pairs with actual statement text.

## Unfinished work

None in the one-level split. The cited open obligations remain their existing DAG items; no additional proof obligations were concealed in a new restatement. The required delivery dry run and push are performed after this report is written.
