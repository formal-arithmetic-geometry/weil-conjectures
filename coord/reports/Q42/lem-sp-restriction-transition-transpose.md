# Stage-1 repair: Q42 / lem-sp-restriction-transition-transpose

1. Files: dag/nodes/sec-smooth-purity/lem-sp-restriction-transition-transpose.json (statement unchanged; four-step assembly); lem-sp-proper-scalar-counit-square.json (statement, unsplit, no Mathlib match); lem-sp-open-scalar-counit-square.json (statement, unsplit, no Mathlib match). citations.json records the complete verbatim statement for every citation. Two new nodes, zero Mathlib leaves.
2. Attachments: none. The project declaration AlgebraicGeometry.ProEtale.restrictionTransitionTranspose in lean/Sheaf/SecSmoothPurity/RestrictionTransitionTranspose.lean:128 ends in sorry at line 216. Searches of lean/WeilConjectures/ by blueprint id and scalar/counit/restriction terminology found no project declaration giving all clauses. Existing module-object and scalar adjunction results do not prove this geometric comparison.
3. WANTED: none.
4. The released repair note of 2026-10-22 explicitly reopens the reviewed live node under keep_plan. The sandbox initially contained only dispatcher markers; no prior node, report or search log existed. The initial required dry run exited with no node files. I copied the current live node, including its proof, citations, searches and metadata, and retained its statement and statement dependencies exactly. The former worker's stale-dispatch disposition is superseded by the released repair note. The mathematical defect being repaired is excessive proof granularity, not a statement dispute.
5. No unfinished stage-1 work is intentionally deferred in the item. The two new argument nodes are deliberately statement-only, with empty proof and proof_deps, so independent workers can start both. No Lean was written or compiled, no repository or launcher file was modified, and no agents were started.

## Review by Q42

I read the chapter sec-smooth-purity and unit sk-prop-sp-tower-geometric, the current blueprint sk-prop-sp-tower-geometric-gluing.proof.md (Levels paragraph, of det-sp-tower-gluing), and sk-lem-sp-reduction-direct-image.proof.md Step 1 (definition by the proper counit and open tensor map) and Step 4 (coefficient composition). I read Stacks sites-cohomology.tex lemma-adjoint (07A6), lemma-derived-pullback-composition (0D6D), lemma-derived-pushforward-composition (0D6E), and sites-modules.tex lemma-j-shriek-and-tensor (0E8I). The new proper statement serves old steps 1-2 and the comparison identification in old step 4; its source is the three sites-cohomology lemmas and the existing explicit mate calculation. The open statement serves old step 3 and the open part of old step 7; its sources are 0E8I, the normalized scalar adjunction, and the sectionwise extension construction. These refinements are agent-formulated; the sources are not claimed to print the exact new equations.

Step 1 cites the new proper node for the ambient scalar counit equation, naturality of gamma and the equality of D with the K-injective direct-image restriction comparison. I read lem-weil-pbc-ring-sheaf-change-adjunction, lem-weil-proetale-direct-image-restriction-of-scalars and lem-weil-pbc-ringed-topoi-derived-pushforward-composition: the first fixes d by the ringed square, the second fixes the inverse representative map, and the third fixes kappa. They have the same orientation after taking D=d inverse. The new proper statement explicitly exposes this identification, rather than losing the reviewer's old Step-4 correction. The two composite geometric/scalar adjunction counits and the characterization of gamma are also stated in that node. Their domains are P_B T_Y R_A r_Z H and T_Y R_A r_Z H respectively, so the cancellation uses D inverse followed by D at the same H. All small pro-etale sites are the project's chosen small presentations. Neither resolution nor comparison assumes scalar restriction preserves K-injectives or finite Tor amplitude.

Step 1 cites the new open node for the equation epsilon_Z J_B T(a)=J_B(epsilon_X) E and the identity open unit. I checked def-weil-extension-by-zero, lem-cbc-proetale-extension-zero, def-sp-reduction-direct-image-comparison and lem-sf-open-tensor-normalization: extension is the sheafification of the presheaf whose values on objects over X are the original sheaf; all covers of such an object stay over X. Hence the unit is the section identity, degreewise and after exact descent. E is the same normalized comparison as in the proper/open construction, not an arbitrary tensor isomorphism. Under restriction both sides become epsilon_X; the fully faithful open adjunction gives equality without any claim that geometric stalks detect unbounded morphisms. I checked the direction T_Z J_A -> J_B T_X and a:J_A r_X -> r_Z J_B in the displayed composite.

The remaining two Step-1 citations say exactly that d_f is the open restriction identification followed by the named direct-image restriction comparison (lem-sf-compact-support-restriction-of-scalars) and b_f is the proper counit map followed by open tensor (det-sp-reduction-direct-image). The representative identification is needed to put their proper factors in the same coordinates. Naturality of gamma at a_L yields the displayed three-factor equality; substituting the open square proves the ambient compact-support counit equation. This assembly step has no argument hidden behind an unspecified comparison.

Step 2 uses the normalized scalar Hom bijection of lem-pur-sheaf-ring-derived-coefficient-adjunction: its inverse is epsilon T(v). Expansion, Step 1 and naturality of b give F_B(epsilon T(t)) b. Naturality in both Hom variables follows from that same statement, and d_f and b are natural by the statements read above. The converse substitution K=r_X L,t=1 is explicitly ambient. det-sp-reduction-direct-image supplies invertibility only on ctf input. I verified that restricting a finite-Tor B-complex to A is never asserted to have finite Tor amplitude.

Step 3 uses the composite-counit and identity-adjunction assertions of lem-sfb-ringed-derived-monoidal-comparisons, the associator and ctf preservation of det-sp-scalar-extension-functor, the composition of d_f from lem-sf-compact-support-restriction-of-scalars, and precisely the printed b-cocycle of det-sp-reduction-direct-image. Substituting the composite counit into epsilon T(v) gives successive transposition under alpha. The d composition fixes the mixed input map, and the printed b-cocycle fixes the output factors; these three equalities are the desired successive-coefficient assertion. The source and target agree using alpha:(K_B)_C -> K_C. No intermediate restricted object is treated as ctf.

Step 4 uses the identity normalization from the same ringed-comparison statement, the new open node's identity normalization, and the proper node's representative normalization. For an identity ring map one can choose the same K-injective resolution; the representative is identity. The open presheaf comparison is identity. Thus d_f=1 and the ambient counit equation makes b_f=1 under scalar unitors; the mixed transpose is F_A(t), which is identity for t=1 by functoriality. No new substantive lemma is needed for this specialization.

I tested the new statements for h=identity, j=identity, the empty open, zero complexes, identity ring maps, and A=Z/ell^2 -> B=Z/ell. For identity geometric maps the proper square reduces to scalar counit naturality; for the empty open both sides are the unique zero map. For the nonflat quotient the counit is still derived and the equations do not replace derived tensor by ordinary tensor. These tests reject the tempting extra hypothesis that r_X L must be ctf. The proper node is independent of openness and works for any h; the open node is independent of properness and works for any open j. They are comparable independent pieces rather than clauses restating the compact-support mixed-map theorem.

I checked delivery-errors B-E: self-contained objects and hypotheses, real source tags/labels, single TeX escapes, definition dependencies, no new proof sketches inside statements, no unsupported citation or reference to another node's proof, no new cycle, no route change and no SGA. Every step is shorter than 2000 characters; the full assembly is 2445 characters. Required searches were run via msearch.py (two semantic phrasings for each new node plus Loogle, grep and LeanSearch). I read the search hits: generic ModuleCat counits, Mates.lean's mateEquiv_counit, presheaf pushforward and O_X-module restriction adjunctions do not identify the specific constant-ring unbounded pro-etale comparison. The generic mate theorem would still require the ringed-square normalization and open unit calculation, so neither new statement is a one-line specialization. Searches for a third possible generic extraction were also logged, but no such node was created because the remaining assembly already follows from existing statements.

## Not duplicates

lem-sp-open-scalar-counit-square vs lem-sbc-derived-restriction-zero-transport: the existing statement concerns Restriction triangle and coefficient transport in degree zero; it does not identify the pro-etale extension-by-zero restriction/tensor comparisons with the scalar counit at arbitrary ambient B-complexes.

lem-sp-open-scalar-counit-square vs lem-sbc-restricted-derived-section-zero-comparison: the existing statement concerns Zeroth comparison for restricted derived section pullback; it does not identify the pro-etale extension-by-zero restriction/tensor comparisons with the scalar counit at arbitrary ambient B-complexes.

lem-sp-open-scalar-counit-square vs lem-sbc-derived-section-pullback-zero: the existing statement concerns Degree-zero derived section pullback before restriction coherence; it does not identify the pro-etale extension-by-zero restriction/tensor comparisons with the scalar counit at arbitrary ambient B-complexes.

lem-sp-open-scalar-counit-square vs lem-sbc-derived-section-single-unit: the existing statement concerns Derived section pullback intertwines the two single-object units; it does not identify the pro-etale extension-by-zero restriction/tensor comparisons with the scalar counit at arbitrary ambient B-complexes.

lem-sp-open-scalar-counit-square vs lem-sbc-restricted-derived-section-shift-comparison: the existing statement concerns Shifted single comparison for restricted derived section pullback; it does not identify the pro-etale extension-by-zero restriction/tensor comparisons with the scalar counit at arbitrary ambient B-complexes.

lem-sp-open-scalar-counit-square vs lem-sbc-restricted-derived-sections-single: the existing statement concerns Single comparison for restricted derived sections before homology; it does not identify the pro-etale extension-by-zero restriction/tensor comparisons with the scalar counit at arbitrary ambient B-complexes.

lem-sp-open-scalar-counit-square vs lem-sbc-restricted-derived-evaluation-pullback: the existing statement concerns The restricted derived section square for arbitrary source sheaves; it does not identify the pro-etale extension-by-zero restriction/tensor comparisons with the scalar counit at arbitrary ambient B-complexes.

lem-sp-open-scalar-counit-square vs lem-sbc-restricted-derived-sections-shift-transport: the existing statement concerns Transport of restricted section pullback through the shift comparison; it does not identify the pro-etale extension-by-zero restriction/tensor comparisons with the scalar counit at arbitrary ambient B-complexes.

lem-sp-open-scalar-counit-square vs lem-coef-enriched-sequence-projection-formula: the existing statement concerns Uncurried finite projections of the enriched sequence adjunction; it does not identify the pro-etale extension-by-zero restriction/tensor comparisons with the scalar counit at arbitrary ambient B-complexes.

lem-sp-open-scalar-counit-square vs lem-coef-scalar-hom-zero-compatibility: the existing statement concerns Degree-zero normalization of scalar internal Hom; it does not identify the pro-etale extension-by-zero restriction/tensor comparisons with the scalar counit at arbitrary ambient B-complexes.

lem-sp-open-scalar-counit-square vs def-coef-compact-support-tensor-comparison: the existing statement concerns Universal coefficient tensor presentations and canonical compact-support coefficient map; it does not identify the pro-etale extension-by-zero restriction/tensor comparisons with the scalar counit at arbitrary ambient B-complexes.

lem-sp-open-scalar-counit-square vs def-sf-ringed-derived-adjoint-lift-data: the existing statement concerns Data of a normalized derived adjoint lift of a ringed-topos morphism; it does not identify the pro-etale extension-by-zero restriction/tensor comparisons with the scalar counit at arbitrary ambient B-complexes.

lem-sp-proper-scalar-counit-square vs lem-sp-restriction-transition-transpose: the existing item concerns a composite Rh_* j_! and arbitrary mixed arrows, naturality and coefficient coherence; this node isolates only the proper normalized square and its K-injective identification, with no compact-support or mixed-map assertion.

lem-sp-proper-scalar-counit-square vs lem-sbc-derived-restriction-zero-transport: the existing statement concerns Restriction triangle and coefficient transport in degree zero; it does not identify the canonical pro-etale direct-image restriction comparison with the geometric-counit mate for arbitrary finite ring maps.

lem-sp-proper-scalar-counit-square vs lem-sbc-restricted-derived-section-zero-comparison: the existing statement concerns Zeroth comparison for restricted derived section pullback; it does not identify the canonical pro-etale direct-image restriction comparison with the geometric-counit mate for arbitrary finite ring maps.

lem-sp-proper-scalar-counit-square vs lem-sbc-derived-section-pullback-zero: the existing statement concerns Degree-zero derived section pullback before restriction coherence; it does not identify the canonical pro-etale direct-image restriction comparison with the geometric-counit mate for arbitrary finite ring maps.

lem-sp-proper-scalar-counit-square vs lem-sbc-derived-section-single-unit: the existing statement concerns Derived section pullback intertwines the two single-object units; it does not identify the canonical pro-etale direct-image restriction comparison with the geometric-counit mate for arbitrary finite ring maps.

lem-sp-proper-scalar-counit-square vs lem-sbc-restricted-derived-section-shift-comparison: the existing statement concerns Shifted single comparison for restricted derived section pullback; it does not identify the canonical pro-etale direct-image restriction comparison with the geometric-counit mate for arbitrary finite ring maps.

lem-sp-proper-scalar-counit-square vs lem-sbc-restricted-derived-sections-single: the existing statement concerns Single comparison for restricted derived sections before homology; it does not identify the canonical pro-etale direct-image restriction comparison with the geometric-counit mate for arbitrary finite ring maps.

lem-sp-proper-scalar-counit-square vs lem-sbc-restricted-derived-evaluation-pullback: the existing statement concerns The restricted derived section square for arbitrary source sheaves; it does not identify the canonical pro-etale direct-image restriction comparison with the geometric-counit mate for arbitrary finite ring maps.

lem-sp-proper-scalar-counit-square vs lem-sbc-restricted-derived-sections-shift-transport: the existing statement concerns Transport of restricted section pullback through the shift comparison; it does not identify the canonical pro-etale direct-image restriction comparison with the geometric-counit mate for arbitrary finite ring maps.

lem-sp-proper-scalar-counit-square vs lem-coef-enriched-sequence-projection-formula: the existing statement concerns Uncurried finite projections of the enriched sequence adjunction; it does not identify the canonical pro-etale direct-image restriction comparison with the geometric-counit mate for arbitrary finite ring maps.

lem-sp-proper-scalar-counit-square vs lem-coef-scalar-hom-zero-compatibility: the existing statement concerns Degree-zero normalization of scalar internal Hom; it does not identify the canonical pro-etale direct-image restriction comparison with the geometric-counit mate for arbitrary finite ring maps.

lem-sp-proper-scalar-counit-square vs def-coef-compact-support-tensor-comparison: the existing statement concerns Universal coefficient tensor presentations and canonical compact-support coefficient map; it does not identify the canonical pro-etale direct-image restriction comparison with the geometric-counit mate for arbitrary finite ring maps.

lem-sp-open-scalar-counit-square vs lem-fix-open-scalar-tensor-normalization: the existing node identifies the scalar open map with the projection formula and its tensor/composition squares; it does not state the scalar-counit square with a:J_A Res -> Res J_B. Our new equation needs this separate open-adjunction argument.

lem-sp-proper-scalar-counit-square vs lem-sfb-ringed-comparison-tensor-adjunction: the existing node states the composite geometric counit for a ringed square, not the further scalar mate equality or the identification with the independently normalized K-injective restriction map. These are explicitly separate statements in the new node.

lem-sp-proper-scalar-counit-square vs lem-sp-proetale-direct-image-scalar-cocycle: the existing node compares A->B->C extension mates, not extension/restriction scalar counits or the normalization of D.

lem-sp-open-scalar-counit-square vs lem-coef-etale-open-tensor: the existing statement is on small etale sites and concerns the geometric open counit, not the scalar counit and restriction comparison on pro-etale sites.

lem-sp-proper-scalar-counit-square vs lem-sf-direct-image-reduction-hom-square: the latter starts with derived-complete completed-ring input and fixed uniformizer quotients; it neither supplies arbitrary finite ring maps nor the ambient proper comparison normalization used here.


lem-sp-open-scalar-counit-square vs def-pd-section-derived-realization: the existing node defines conjugate section-module tensor and geometric realization constructions for a condensed coefficient; it makes no assertion about a change of finite rings or its scalar counit. The new node asserts the specified open restriction/tensor scalar-counit square and its open-unit normalization.

lem-sp-open-scalar-counit-square vs def-pd-section-derived-tensor-data: the existing node defines tensor and localization data for the internal/section-module equivalence at one condensed coefficient; it does not assert a varying-ring scalar-counit square. The new node asserts the specified open restriction/tensor scalar-counit square and its open-unit normalization.

lem-sp-open-scalar-counit-square vs lem-pd-module-ringed-topos-derived-comparison: the existing node identifies internal modules with section modules and their geometric operations at one condensed coefficient; it neither identifies D for a finite ring map nor states the scalar-counit equation for open extension. The new node asserts the specified open restriction/tensor scalar-counit square and its open-unit normalization.

lem-sp-open-scalar-counit-square vs lem-pd-section-derived-pushpull-normalization: the existing node compares geometric operations under the fixed section equivalence, with no coefficient change and no extension/restriction scalar square. The new node asserts the specified open restriction/tensor scalar-counit square and its open-unit normalization.

lem-sp-open-scalar-counit-square vs def-pbc-successive-derived-scalar-normalization-data: the existing node is a type of normalization witnesses for two scalar extensions; it explicitly asserts no existence, and has no geometric direct image or extension by zero. The new node asserts the specified open restriction/tensor scalar-counit square and its open-unit normalization.

lem-sp-open-scalar-counit-square vs def-weil-pbc-derived-direct-image-composition: the existing node defines the geometric direct-image compositor on bounded-below abelian etale categories; it has no finite-ring scalar functors or unbounded pro-etale scalar-counit assertion. The new node asserts the specified open restriction/tensor scalar-counit square and its open-unit normalization.

lem-sp-open-scalar-counit-square vs def-weil-pbc-derived-normalization-arrows: the existing node defines constant-sheaf normalization arrows and an underived inverse-image coefficient mate; it has neither the direct-image scalar-counit equation nor the derived open-extension scalar-counit equation. The new node asserts the specified open restriction/tensor scalar-counit square and its open-unit normalization.

lem-sp-open-scalar-counit-square vs def-weil-pbc-ringed-slice-derived-data: the existing node packages normalized adjunction and slice comparison witnesses; it supplies no existence or equality for the specified finite-ring proper/open scalar comparisons. The new node asserts the specified open restriction/tensor scalar-counit square and its open-unit normalization.

lem-sp-open-scalar-counit-square vs def-weil-pbc-successive-derived-quotient-data: the existing node defines successive scalar-extension normalization data rather than proving their existence, and includes no geometric direct-image or open-extension assertion. The new node asserts the specified open restriction/tensor scalar-counit square and its open-unit normalization.

lem-sp-open-scalar-counit-square vs lem-pbc-normalized-derived-adjunction-transport: the existing node transports derived adjunction data across additive equivalences subject to ordinary-unit compatibility; coefficient restriction is not such an equivalence for general A to B, and the needed geometric proper/open comparisons are absent. The new node asserts the specified open restriction/tensor scalar-counit square and its open-unit normalization.

lem-sp-open-scalar-counit-square vs lem-weil-pbc-cohomology-pullback-derived-unit: the existing node identifies bounded-below abelian etale cohomology pullback with a geometric adjunction unit and Leray; it has no scalar extension/restriction square or open extension. The new node asserts the specified open restriction/tensor scalar-counit square and its open-unit normalization.

lem-sp-open-scalar-counit-square vs lem-weil-pbc-derived-adjunction-shift: the existing node asserts shift compatibility for one canonical geometric derived adjunction; it has no change-of-rings comparison or open-extension counit square. The new node asserts the specified open restriction/tensor scalar-counit square and its open-unit normalization.

lem-sp-proper-scalar-counit-square vs def-pd-section-derived-realization: the existing node defines conjugate section-module tensor and geometric realization constructions for a condensed coefficient; it makes no assertion about a change of finite rings or its scalar counit. The new node asserts the specified proper scalar-counit square, its composite-counit coordinates and the equality with the independently normalized K-injective restriction comparison.

lem-sp-proper-scalar-counit-square vs def-pd-section-derived-tensor-data: the existing node defines tensor and localization data for the internal/section-module equivalence at one condensed coefficient; it does not assert a varying-ring scalar-counit square. The new node asserts the specified proper scalar-counit square, its composite-counit coordinates and the equality with the independently normalized K-injective restriction comparison.

lem-sp-proper-scalar-counit-square vs lem-pd-module-ringed-topos-derived-comparison: the existing node identifies internal modules with section modules and their geometric operations at one condensed coefficient; it neither identifies D for a finite ring map nor states the scalar-counit equation for open extension. The new node asserts the specified proper scalar-counit square, its composite-counit coordinates and the equality with the independently normalized K-injective restriction comparison.

lem-sp-proper-scalar-counit-square vs lem-pd-section-derived-pushpull-normalization: the existing node compares geometric operations under the fixed section equivalence, with no coefficient change and no extension/restriction scalar square. The new node asserts the specified proper scalar-counit square, its composite-counit coordinates and the equality with the independently normalized K-injective restriction comparison.

lem-sp-proper-scalar-counit-square vs def-pbc-successive-derived-scalar-normalization-data: the existing node is a type of normalization witnesses for two scalar extensions; it explicitly asserts no existence, and has no geometric direct image or extension by zero. The new node asserts the specified proper scalar-counit square, its composite-counit coordinates and the equality with the independently normalized K-injective restriction comparison.

lem-sp-proper-scalar-counit-square vs def-weil-pbc-derived-direct-image-composition: the existing node defines the geometric direct-image compositor on bounded-below abelian etale categories; it has no finite-ring scalar functors or unbounded pro-etale scalar-counit assertion. The new node asserts the specified proper scalar-counit square, its composite-counit coordinates and the equality with the independently normalized K-injective restriction comparison.

lem-sp-proper-scalar-counit-square vs def-weil-pbc-derived-normalization-arrows: the existing node defines constant-sheaf normalization arrows and an underived inverse-image coefficient mate; it has neither the direct-image scalar-counit equation nor the derived open-extension scalar-counit equation. The new node asserts the specified proper scalar-counit square, its composite-counit coordinates and the equality with the independently normalized K-injective restriction comparison.

lem-sp-proper-scalar-counit-square vs def-weil-pbc-ringed-slice-derived-data: the existing node packages normalized adjunction and slice comparison witnesses; it supplies no existence or equality for the specified finite-ring proper/open scalar comparisons. The new node asserts the specified proper scalar-counit square, its composite-counit coordinates and the equality with the independently normalized K-injective restriction comparison.

lem-sp-proper-scalar-counit-square vs def-weil-pbc-successive-derived-quotient-data: the existing node defines successive scalar-extension normalization data rather than proving their existence, and includes no geometric direct-image or open-extension assertion. The new node asserts the specified proper scalar-counit square, its composite-counit coordinates and the equality with the independently normalized K-injective restriction comparison.

lem-sp-proper-scalar-counit-square vs lem-pbc-normalized-derived-adjunction-transport: the existing node transports derived adjunction data across additive equivalences subject to ordinary-unit compatibility; coefficient restriction is not such an equivalence for general A to B, and the needed geometric proper/open comparisons are absent. The new node asserts the specified proper scalar-counit square, its composite-counit coordinates and the equality with the independently normalized K-injective restriction comparison.

lem-sp-proper-scalar-counit-square vs lem-weil-pbc-cohomology-pullback-derived-unit: the existing node identifies bounded-below abelian etale cohomology pullback with a geometric adjunction unit and Leray; it has no scalar extension/restriction square or open extension. The new node asserts the specified proper scalar-counit square, its composite-counit coordinates and the equality with the independently normalized K-injective restriction comparison.

lem-sp-proper-scalar-counit-square vs lem-weil-pbc-derived-adjunction-shift: the existing node asserts shift compatibility for one canonical geometric derived adjunction; it has no change-of-rings comparison or open-extension counit square. The new node asserts the specified proper scalar-counit square, its composite-counit coordinates and the equality with the independently normalized K-injective restriction comparison.

## Preservation of the returned seven arguments

The following is the entire former proof, copied verbatim. It is working material for the two future workers and the maintainer, not proof steps or proof_deps of the new statement-only nodes. The short assembly does not erase this material.

Coverage: old step 1's scalar transpose formula is assembly step 2; its geometric/scalar notation, gamma characterization and unbounded hypothesis are the proper node. Old step 2 is the proper node's composite-counit and scalar-counit equations; its Hom-injectivity calculation is retained below. Old step 3 is the open node, including the sectionwise unit and Hom-detection normalization. Old step 4's representative comparison identification is the proper node; its compact-support paste and gamma naturality are assembly step 1. Old step 5 is assembly step 2. Old step 6 is assembly step 3 using the same existing general coherence statements. Old step 7's open identity is the open node and its proper/scalar identity argument is assembly step 4. Thus every former inference is either an explicitly stated task of a new worker or the explicit assembly of already cited statements; no statement was replaced by a weaker assertion.

### Former step 1

Work throughout in the ordinary ambient derived categories, and abbreviate restriction by $r$. By [lem-pur-sheaf-ring-derived-coefficient-adjunction] the adjunction $T_W\dashv r_W$ exists on these unbounded categories, with its specified tensor normalization. Thus the transpose of $v:M\to r_WH$ is
$$v^\sharp=\epsilon_W(H)\circ T_W(v).$$
Put $Z=\overline X$, $P_R=h_R^*$, $R_R=Rh_{*,R}$ and $J_R=j_{!,R}$. The geometric adjunction $P_R\dashv R_R$ is the one in [def-weil-pbc-proetale-operations]; denote its counit by $e^R$, reserving $\epsilon$ for scalar adjunctions. The constant-ring maps needed for these adjunctions are canonical by [prop-weil-pbc-proetale-constant-ring-map]. Write
$$D:R_A r_Z\xrightarrow{\sim}r_YR_B$$
for the inverse of the comparison called $d$ in [lem-weil-pbc-ring-sheaf-change-adjunction], and $\chi:P_BT_Y\xrightarrow{\sim}T_ZP_A$ for the canonical pullback/scalar comparison. The proper part of the comparison in [det-sp-reduction-direct-image] is $\gamma_N:T_YR_AN\to R_BT_ZN$, characterized by
$$e^B_{T_ZN}\circ P_B(\gamma_N)=T_Z(e^A_N)\circ\chi_{R_AN}.$$
No assertion that $r_Z$ preserves finite Tor amplitude is made or needed.

### Former step 2

For $H\in D(Z_{\mathrm{proet}},B)$ the two factorizations of the same ringed-topos morphism $(Z,B_Z)\to(Y,A_Y)$ have composite adjunctions
$$P_BT_Y\dashv r_YR_B,\qquad T_ZP_A\dashv R_Ar_Z.$$
Their canonical left comparison is $\chi$, and their right comparison is $D^{-1}$. The adjunction-compatible composition and composite-counit assertion of [lem-sfb-ringed-derived-monoidal-comparisons], applied to this square, gives explicitly
$$e^B_H\circ P_B(\epsilon_Y(R_BH))\circ\chi^{-1}_{r_YR_BH}
=\epsilon_Z(H)\circ T_Z(e^A_{r_ZH})\circ T_ZP_A(D_H^{-1}).$$
Here the right comparisons are precisely the direct-image coefficient comparison by [lem-weil-pbc-ring-sheaf-change-adjunction]. Precompose by $\chi_{r_YR_BH}\circ P_BT_Y(D_H)$ and use naturality of $\chi$. The factors $T_ZP_A(D_H^{-1})$ and $T_ZP_A(D_H)$ cancel. Hence the $P_B\dashv R_B$ transpose of $\epsilon_Y(R_BH)\circ T_Y(D_H)$ is
$$\epsilon_Z(H)\circ T_Z(e^A_{r_ZH})\circ\chi_{R_Ar_ZH}.$$
The transpose of $R_B(\epsilon_Z(H))\circ\gamma_{r_ZH}$ is the same: move $R_B(\epsilon_Z(H))$ through the geometric counit by naturality and use Step 1. Injectivity of this Hom bijection therefore proves
$$\epsilon_Y(R_BH)\circ T_Y(D_H)=R_B(\epsilon_Z(H))\circ\gamma_{r_ZH}.$$
This calculation is on arbitrary $H$, even when $r_ZH$ is unbounded or has infinite Tor amplitude.

### Former step 3

Let $a_L:J_Ar_XL\xrightarrow{\sim}r_ZJ_BL$ be the open restriction comparison of [lem-cbc-proetale-extension-zero], and let $E_M:T_ZJ_AM\xrightarrow{\sim}J_BT_XM$ be the canonical open tensor comparison used in [det-sp-reduction-direct-image]. It satisfies
$$\epsilon_Z(J_BL)\circ T_Z(a_L)=J_B(\epsilon_X(L))\circ E_{r_XL}.$$
Indeed the domain is identified by $E_{r_XL}$ with $J_BT_Xr_XL$. Under $J_B\dashv j^{-1}$ from [lem-cbc-proetale-extension-zero], maps from this domain to $J_BL$ are determined by restriction to $X$. The unit $M\to j^{-1}J_BM$ is the identity: in [def-weil-extension-by-zero], the defining presheaf on every object over $X$, and on every covering of it, is $M$, so its sheafification restricts to $M$. This holds degreewise and descends since the two functors are exact. After restriction, $a$ and $E$ are the identity comparisons of restriction and tensor on $X$. Both displayed maps then become $\epsilon_X(L)$ by the representative normalization of [lem-pur-sheaf-ring-derived-coefficient-adjunction]. The Hom bijection gives the claimed equality without a stalk-detection argument.

### Former step 4

By [lem-sf-compact-support-restriction-of-scalars], the specified compact-support comparison is $R_A(a_L)$ followed by the direct-image comparison of [lem-weil-proetale-direct-image-restriction-of-scalars] at $J_BL$. That comparison is $D$: for a K-injective complex $I$ of $B_Z$-modules and a K-injective resolution $r_ZI\to I'$, its value is the inverse of $r_Yh_*I=h_*r_ZI\to h_*I'$. By the normalization of $\kappa$ in [lem-weil-pbc-ringed-topoi-derived-pushforward-composition] applied to the two factorizations of Step 2 (the factor $r_Y$ being exact), the comparison $d$ of [lem-weil-pbc-ring-sheaf-change-adjunction] at $I$ is the class of that same map. Hence
$$d_f(L)=D_{J_BL}\circ R_A(a_L).$$
By the proper-counit and open-tensor normalization of [det-sp-reduction-direct-image], its scalar-extension comparison is
$$b_f(M)=R_B(E_M)\circ\gamma_{J_AM}.$$
Apply Step 2 to $H=J_BL$, then use naturality of $\gamma$ at $a_L$ and Step 3. It gives
$$\begin{aligned}
\epsilon_Y(F_{f,B}L)\,T_Y(d_f(L))
&=R_B(\epsilon_Z(J_BL))\,\gamma_{r_ZJ_BL}\,T_YR_A(a_L)\\
&=R_B\bigl(\epsilon_Z(J_BL)\,T_Z(a_L)\bigr)\,\gamma_{J_Ar_XL}\\
&=R_BJ_B(\epsilon_X(L))\,R_B(E_{r_XL})\,\gamma_{J_Ar_XL}\\
&=F_{f,B}(\epsilon_X(L))\,b_f(r_XL).
\end{aligned}$$
Naturality of $\gamma$ follows directly from its defining transpose in Step 1: for $u:N\to N'$ both transposes are $T_Z(u\,e^A_N)\chi_{R_AN}$, by naturality of $e^A$ and $\chi$. Thus its use here is valid in the ambient categories, without assuming that $r_XL$ is in $\Dctf$. This proves precisely the required counit equation.

### Former step 5

Now use the scalar transpose formula of Step 1, the counit equation of Step 4, and naturality of $b_f$ at $t:K\to r_XL$:
$$\begin{aligned}
\bigl(d_f(L)F_{f,A}(t)\bigr)^\sharp
&=\epsilon_Y(F_{f,B}L)\,T_Y(d_f(L))\,T_YF_{f,A}(t)\\
&=F_{f,B}(\epsilon_X(L))\,b_f(r_XL)\,T_YF_{f,A}(t)\\
&=F_{f,B}\bigl(\epsilon_X(L)T_X(t)\bigr)\,b_f(K)
=F_{f,B}(t^\sharp)\,b_f(K).
\end{aligned}$$
The ambient naturality used here follows from $b_f=R_B(E)\gamma J_A$: $E$ is the natural tensor comparison and naturality of $\gamma$ was checked in Step 4. The scalar adjunction of [lem-pur-sheaf-ring-derived-coefficient-adjunction] is natural in both variables, so this equality is natural in $K,L,t$. Conversely, setting $K=r_XL$, $t=1$, in this ambient calculation recovers Step 4, since $t^\sharp=\epsilon_X(L)$. This substitution is in the ambient categories and does not assert finite Tor amplitude for $r_XL$. Invertibility on $\Dctf$ input is exactly the assertion of [det-sp-reduction-direct-image]; no inversion was used in the calculation.

### Former step 6

For $A\to B\to C$, write $T^{A,B}$ and $r^{A,B}$ for the scalar functors. The composite scalar adjunction has counit
$$\epsilon_W^{B,C}\circ T_W^{B,C}(\epsilon_W^{A,B}):T_W^{B,C}T_W^{A,B}r_W^{A,B}r_W^{B,C}\longrightarrow1.$$
By the composition normalization of [lem-sfb-ringed-derived-monoidal-comparisons], this is the $A\to C$ counit under the tensor associator $\alpha$ of [det-sp-scalar-extension-functor]. In particular two successive transposes of a map $K\to r_X^{A,B}r_X^{B,C}L$ are its direct $A\to C$ transpose, precomposed with $\alpha_K$. The restriction comparisons compose by [lem-sf-compact-support-restriction-of-scalars]. Finally [det-sp-reduction-direct-image] gives the explicit equality of the coefficient transformations on $K\in\Dctf(X,A)$:
$$b_{A,C}(K)\alpha_{F_{f,A}K}=F_{f,C}(\alpha_K)\,b_{B,C}(T_X^{A,B}K)\,T_Y^{B,C}(b_{A,B}(K)).$$
These three equations identify respectively the transposes, the mixed-coefficient input maps, and the comparison factors in the formula of Step 5 for successive and composite coefficient change. They prove its required compatibility. The intermediate $T_X^{A,B}K$ lies in $\Dctf(X,B)$ by [det-sp-scalar-extension-functor]. All scalar counits themselves are ambient maps, so no hypothesis on the Tor amplitude of a restricted $C$-object is introduced.

### Former step 7

For an identity coefficient map, the canonical identity normalization of [lem-sfb-ringed-derived-monoidal-comparisons] identifies scalar extension, restriction and their adjunction with the identity adjunction. The comparison $d_f$ is the identity: the open restriction comparison is the identity on the defining presheaf [def-weil-extension-by-zero], and the proper comparison is the canonical direct-image identity comparison. In the counit equation of Step 4 this gives $b_f=1$. Hence the formula of Step 5 becomes $F_{f,A}(t)$, and if $t=1_K$ it is $1_{F_{f,A}K}$ by functoriality. The derivation used no flatness of $B/A$: the scalar and geometric adjunctions and composite normalizations used above are unbounded and permit nonflat ring maps, as stated in [lem-pur-sheaf-ring-derived-coefficient-adjunction] and [lem-sfb-ringed-derived-monoidal-comparisons].


## Verification notes

The first populated dry run exited at the same-tag duplicate check, before pushing. I opened all twelve additional named statements and added the distinctions above. These include data-definition nodes (which assert no existence) and transport statements for condensed section equivalences, bounded-below etale abelian categories or shifts; none states either new counit-square theorem.

## Return repair: live-DAG promotion, 2026-10-22

The return identifies the retained delivery as fb42933df30 and approves its mathematics; landing failed because the side completion had not been promoted to the live DAG. I treated the retained sandbox as that returned packet, compared it with the current shared read clone, and ran the required delivery tool, which constructs its overlay on current origin/sheaf-dag. Its first dry run passed at bf9b0d23729. The current item still has the seven-step proof; the retained packet differs only in proof, proof_deps and split_report, with its statement, statement dependencies and all other fields identical. Neither of the two new node ids exists in the current DAG. The released stage-1 repair order still applies.

I re-read every assembly dependency and the two new statements. All 13 retained citation quotes are complete statements and still match the current DAG verbatim; hence no changed cited mathematical statement requires a replacement argument. In Step 1 the proper node supplies the counit square and representative identification, the open node supplies its counit square, and compact-support-restriction-of-scalars supplies the composition and its orientation. In Steps 2-4 the scalar-adjunction statement still supplies the normalized Hom transpose, the ringed-derived-monoidal statement supplies the composite and identity counits, scalar-extension-functor supplies the associator and ctf preservation, and reduction-direct-image supplies ctf invertibility and the printed coefficient cocycle. I also re-read the new nodes' definition dependencies and the three direct-image normalization statements: their K-injective inverse representative still agrees with D=d inverse.

I made two concrete clarifications in the rebased split. Step 1 now also cites def-sp-reduction-direct-image-comparison, whose statement explicitly defines the natural proper/open composite on the entire ambient category. This makes the use of b on r_X L independent of the ctf-only invertibility assertion in reduction-direct-image. Step 4 now spells out the identity-coefficient representative: choose the same K-injective I with resolution map 1, making D the inverse of 1. citations.json was regenerated from the current statements, including this added citation. No new searches are needed: both new statements and their search questions are unchanged, and I read and retained every recorded search result.

I re-read the current blueprint Levels paragraph and reduction-direct-image Steps 1 and 4, together with Stacks sites-cohomology lemma-adjoint (07A6), lemma-derived-pullback-composition (0D6D), lemma-derived-pushforward-composition (0D6E), and sites-modules lemma-j-shriek-and-tensor (0E8I). These give the same route. I checked the returned packet again against delivery-errors B-E: both supporting nodes remain self-contained statement-only tasks; neither asserts the compact-support mixed-map theorem itself; the compactification, finite-ring and unbounded-category hypotheses match; every actual proof citation has its exact statement in citations.json; no long step hides an additional argument. The identity, empty-open, zero-complex and nonflat quotient cases remain valid. The source Lean declaration still ends in sorry, and the project search gives no full attachment. No repository or launcher file was written, no compiler was run, and no agent was started.
