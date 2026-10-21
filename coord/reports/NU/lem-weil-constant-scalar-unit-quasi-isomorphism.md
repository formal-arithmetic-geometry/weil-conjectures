# Stage-1 report: lem-weil-constant-scalar-unit-quasi-isomorphism

## Files written

- `dag/nodes/sec-smooth-purity/lem-weil-constant-scalar-unit-quasi-isomorphism.json`: existing statement, now split into eight steps; statement unchanged; no Mathlib match.
- `citations.json`: nineteen step/node entries with verbatim statement passages.
- `searches.jsonl`: actual msearch log; six new recorded searches, including two semantic phrasings.
- `report.md`: this report. `prepare.py` is sandbox-only preparation material, not a DAG delivery file.

No new nodes, no Mathlib leaves, no Lean files, and no unit or chapter changes.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, `constantCoefficientScalarUnit`, scalar-unit notions, and repleteness/tower infrastructure. No project declaration states the entire item. `WeilConjectures.constantCoefficientScalarUnit_isIso` in `lean/Sheaf/Paper/ConstantCoefficientScalarNormalization.lean:93` has `sorry` at line 95, as does its uniquely normalized chain-map existence input at line 77. This is source material, not an attachment. The upstream `DerivedLimitEpimorphicTower.lean` theorem is about a general homotopy-limit cone and covers neither this specified scalar unit nor all the item's clauses.

## WANTED

None newly required. The arithmetic inputs already have their own DAG statements and splits. Their historical source metadata mentions Serre's Local Fields; this delivery neither introduces a new arithmetic assertion nor claims to have read that unobtained book.

## Corrections and scope

The item had a statement and searches but no proof. Its full statement is retained. The main potential gap was the difference between an abstract isomorphism with a derived limit and a quasi-isomorphism for the prescribed strict chain map. Step 5 now applies the existing kernel-to-cocone theorem and uses the strict-unit uniqueness to identify that very comparison. Step 7 records the equality of quotient projections after composing with its inverse. No hypothesis or conclusion was changed.

The coefficient category throughout is modules over the completed ring sheaf `R_L`, not modules over the discrete constant ring. The surjective-tower tool explicitly quantifies over an arbitrary commutative ring sheaf. The elementary limit calculation includes the `R_L` action and all the projections.

## Not duplicates

There are no new nodes and therefore no new/existing pairs to distinguish. The argument reuses `lem-weil-proetale-surjective-tower-derived-limit` and `lem-weil-degreewise-epi-kernel-cocone-qis`. Blueprint searches for `epimorphic`, `scalar unit`, and `constant coefficient` were read; the general epimorphic-tower blueprint node is an available tool, not an alternative statement of the normalized scalar-unit item. No blueprint node states this entire normalization/completeness assertion. The item's existing ancestor and exact coefficient-object place are preserved, with `same_as: []`.

## Review by NU

I read the chapter record `sec-smooth-purity`, the unit record `sk-def-sf-admissible`, the ancestor statement `def-weil-ordinary-compact-cohomology`, and the current item. This concerns the ancestor's completed coefficient object and scalar extensions; it does not change the chapter or replace a unit proof route. Off-unit arithmetic, sheafification, module-limit, and kernel-to-cone lemmas are explicitly declared as generic tools in `split_report.tool_uses`.

For the item's source I read Bhatt–Scholze Proposition 3.1.10 and its proof on p. 17, together with Proposition 3.1.9, Proposition 3.2.3(1) on p. 18, Proposition 4.2.8 on p. 29, Definition 3.5.2 on p. 24, and Lemma 6.8.2(1) on pp. 58–59. In particular Proposition 4.2.8 is for any scheme; the qcqs assumption in the following remark is irrelevant. Proposition 3.1.10 proves surjectivity of the difference map and identifies the ordinary limit with the derived limit; it does not alone specify our normalized chain map. The additional strict-coordinate argument is identified as agent-written in `proof_origin`. I also read the source normalization file, whose docstring gives the same quotient-tower argument but whose proof is still sorry.

For Step 1 I opened both cited arithmetic node statements. The finite-extension DVR theorem supplies precisely the DVR and finite-residue hypotheses of the valued-DVR finite-quotient theorem. The given coefficient datum fixes the nonarchimedean absolute value and a maximal-ideal generator, so the latter theorem applies with K=L, O=O_L and pi=varpi_L. Its clauses 2 and 3 assert finiteness and surjective transitions. The proof needs no relation between ramification indices beyond the coefficient maps already fixed in the statement.

For Step 2 I checked the actual statements of the constant-sheaf definition, the generic ring-sheafification underlying-sets lemma, the site-wide sheafification local-section lemma, and the module-sheaf category definition. The first two permit applying the third to the underlying constant ring sheaf, on this pro-etale site, rather than applying an etale-only local-constancy node. I read Stacks `sites.tex`, Tag 00YR (`section-sheaves-algebraic-structures`, assertions beta and gamma) and Tag 00WK (`lemma-sections-sheafification`). Choosing representatives in the surjective finite-ring quotient gives the local lifts. The cited module definition says exactly that cokernels are sheafifications of sectionwise cokernels, so the local lift calculation proves module epimorphy without assuming sectionwise surjectivity on every site object. This argument is elementary relative to those cited statements.

For Step 3 I opened `lem-weil-constant-scalar-strict-unit` and used only its statement: its multiplication maps are actual isomorphisms with inverse z mapped to 1 tensor z and commute with every transition. I did not assume this unsplit node was already proved. I also opened the completed-integral-coefficient definition and the generic module-limit node. The former defines R_L by the quotient limit and its projections; the latter states that module limits are computed on sections with componentwise action. I read Stacks `sites-modules.tex`, Tag 03DB (`lemma-limits-colimits`), including the proof constructing that module action. Thus the coordinate identification is an R_L-linear limit identification and not a mere bijection of sets. No new lemma is hidden here: both inverse maps are the tuple of quotient projections and its limit universal map.

For Step 4 the full statement of `lem-weil-proetale-surjective-tower-derived-limit` explicitly allows a general commutative ring sheaf R on the small pro-etale site of an arbitrary scheme. Its clause 1 is exactly the epimorphic difference map and kernel assertion used. Step 2 verifies its epimorphic transitions; Step 3 verifies the module tower and ordinary limit. This avoids relying on an unmentioned agreement of constant-module and ring-sheaf categories.

For Step 5 I opened the full statement of `lem-weil-degreewise-epi-kernel-cocone-qis`, including the differential and both coordinates. The hypothesis is a degreewise epimorphism of complexes in an abelian category, provided by Step 4 and the cited module category definition. The source and target vanish in every degree except zero. Its comparison has coordinates (zero, inclusion), so its shifted-product component vanishes and the other component has the specified quotient coordinates. The strict-unit statement gives uniqueness with exactly these two conditions, and hence equality with eta. This is a comparison of chain maps, not just agreement of isomorphism classes. I read the cone/short-exact-sequence discussion of Stacks `derived.tex` and Tag 0152 (`lemma-derived-canonical-delta-functor`) while checking the background; the proof itself cites the existing precise kernel comparison rather than attributing that coordinate refinement to Bhatt–Scholze.

For Step 6 clause 2 of the same surjective-tower statement expressly supplies both the product in the derived category with its projections and the distinguished triangle with first arrow the ordinary-limit inclusion. The two assertions are not inferred from a definition or from existence of an unspecified derived limit. Transport through the tower multiplication isomorphism preserves each projection, so the first arrow has exactly the displayed components. I read the derived-limit definition and checked the 1-s sign convention against its Stacks 08TC source and the t-id sign in Bhatt–Scholze.

For Step 7 the derived-category definition states that Q localizes at quasi-isomorphisms, the scalar-extension definition gives the very strict cone for a K-flat representative, and the strict-unit statement supplies K-flatness of the regular representative. The equality j_m eta = u_m^{-1} pi_m is already an equality of chain maps. Multiplication by the inverse of Q(eta) gives the required inverse projection identity without an additional naturality or uniqueness theorem.

For Step 8 the strict-unit statement identifies the self-extension's derived reduction units, not merely the quotient objects. The derived-completeness definition requires a distinguished Roos triangle whose first map has those prescribed unit components. Step 6 provides exactly that triangle, so the criterion applies without adding a completeness assumption. I checked E=L, a ramified E subset L, m=1, disconnected Y, and the empty scheme. Neither the general tower theorem nor the chain-comparison theorem needs finite type or connectedness; on the empty site the module category is zero and the formulas remain valid. No uniformizer power of E is silently identified with a uniformizer power of L.

I read all six msearch results as returned. The second semantic query finds `CochainComplex.mappingCone.quasiIso_descShortComplex`, which I checked in Mathlib's HomotopyCategory/ShortExact and DerivedCategory/ShortExact sources. It is a general cone-to-third-term comparison for a short exact complex, not this normalized coefficient-unit theorem. The module-sheaf limit hits in `Sheaf/Limits.lean` supply ordinary limits only. The first semantic query returns unrelated scheme normalization facts, and Loogle has zero hits. Thus the item remains a split, with no claimed Mathlib match and no fabricated search. Existing searches in the imported item were preserved.

All eight proof steps are shorter than 2000 characters (maximum 891); none hides a new independently formulated sub-claim. Each cited node's statement was opened, and `citations.json` copies its statement or the exact clauses used. All non-elementary inputs are existing cited nodes; the remaining steps explicitly perform the local lifts, coordinate computation, inverse composition, or direct application of the completeness definition. This addresses B1–B10, C1–C8, D1–D5 and E1–E7 with no new-node, circularity, or statement-dispute issue found.

## Unfinished work

None in the stage-1 split. This does not assert that the cited unsplit inputs or sorried Lean declarations are proved. The independent maintainer review remains the next review of the delivery.

## Validation

Server check_dag and review_split both passed. The first full dry run flagged the phrase “the item’s projection names” in Step 5 under its self-containedness wording check. I removed that contextual phrase; the formulas still use the projections explicitly introduced in the node statement. No mathematics, citation or statement changed.
