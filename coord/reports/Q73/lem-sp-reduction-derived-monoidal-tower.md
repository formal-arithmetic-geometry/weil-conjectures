# Stage-1 delivery: lem-sp-reduction-derived-monoidal-tower

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-reduction-derived-monoidal-tower.json: statement, split into eight proof steps; no Mathlib match.
- citations.json: one entry per step/node citation, with verbatim statement quotations.
- report.md: this report.

No new nodes; no Mathlib leaves. The sandbox scripts and searches.jsonl are working material, not additional DAG deliveries. I continued the interrupted attempt, retained its eight-step route, explicit formulas and all inherited searches, and read the recorded search results before using them. The first resumed dry run exited with the missing-report diagnostic; no push had taken place.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag, reduction/monoidal combinations, sequence-site terms and the coefficient-tower notion found no declaration proving all clauses. CompletedIntegral.lean supplies coefficient rings/restriction constructions, and Adic/Reduction.lean treats reductions of completion on the etale side; neither is the coherent unbounded derived-system tensor and geometric-pullback assertion here. Project declarations that prove a different category's statement do not qualify as attachments.

## Literature wanted

None.

## Corrections and route

The live item has no proof. Its mathematical statement and statement dependencies have been retained. The imported text contained a literal newline followed by u where the TeX macro nu was intended, in the display and the list of comparisons. This delivery repairs that escape only; no hypothesis or conclusion is changed and there is no mathematical STATEMENT-DISPUTED claim.

I read the chapter and unit records, SETUP's three levels and GOAL. This item implements paragraph (3) of the current main-20261015 direct-image proof, within sk-prop-sp-integral-adjunction. It proves the generic pullback/tensor reduction prerequisite, without replacing either step of the unit. It is not the unit's key statement, so no realization fields are edited. No SGA source is used.

The earlier attempt used the constant-sequence projection as a ringed-topos morphism; that route is retained. It constructs morphisms of derived systems before evaluating. It does not infer equality of derived-system morphisms from their evaluations. I replaced the earlier inline proof of K-flatness and flat terms of an unbounded total tensor by the existing lem-pur-kflat-total-tensor-model, which states exactly that assertion and its reassociation. I corrected the Stacks labels: the sequence-site section is 0940 (0941 is the derived-limit comparison), and tensor-product-K-flat is 07A2 (06YP is a quasi-isomorphism lemma).

## Mathlib and duplicate searches

The item inherited five search records from its creation. Its own sandbox searches.jsonl records the subsequent grep, LeanSearch, Loogle, and two differently phrased LeanFinder queries. These records and their results were read and retained without claiming any unrun search. The grep and Loogle queries returned no matches. LeanSearch returned ordinary scalar extension, ordinary sheaf pullback and tensor/pushout results. LeanFinder returned ordinary flat-module tensor and generic linear/condensed category instances. None states the simultaneous unbounded derived reduction of a strict varying-ring tower with geometric pullback and the actual quotient transitions. No service in those sandbox records was unavailable.

Whole-DAG concept/tag searches found the sequence-site projection, generic K-flat resolution, K-flat pullback, total tensor model, localization descent, scalar extension and derived monoidal composition nodes reused here. Blueprint searches for sequence site, reduction derived monoidal and K-flat total tensor found no same-statement blueprint node; the broader derived-tensor search supplies generic notions rather than another statement of this whole item. The ancestor tool gives det-sp-integral-direct-image-tower, whose paragraph (3) is recorded in blueprint.from.place and split_report.blueprint. No new node is proposed, so there are no new-vs-existing same-tag pairs.

## Not duplicates

No new nodes. In particular the generic unbounded total-tensor fact was reused as lem-pur-kflat-total-tensor-model rather than duplicated.

## Review by Q73

I read coord/delivery-errors.md B through E, the current item, the source paragraph (3) of sk-prop-sp-integral-adjunction-direct-image.proof.md, and every statement listed in citations.json. I read Stacks sites-cohomology.tex at section-derived-limits (0940), lemma-tensor-product-K-flat (07A2), lemma-pullback-K-flat (0G7E), lemma-derived-pullback-composition (0D6D), and lemma-pullback-tensor-product (07A4), including the representative proof; in sites-modules.tex I read lemma-tensor-product-pullback (03EL), lemma-tensor-commute-colimits (03EP), lemma-colimits-flat (03EU), and lemma-tensor-flats (0G6Q). No new node needs a separate source review. The proof is marked agent-written because the sequence-site specialization, local normalization checks and their assembly extend the blueprint paragraph.

Step 1 uses lem-pur-sequence-site-completion-projection. Its statement supplies the ringed sequence site, exact equivalence with strict semilinear systems, constant/limit geometric morphism, structural completion projections, and computation of its derived pullback by one flat-term K-flat complex with the actual transitions. Those are precisely the data the step uses. The pro-etale site is chosen small in the module universe, and B=lim B_n is exactly R_T, not an unrelated constant ring. This is an existing theorem used as a generic tool, not a clause of this item's tensor theorem disguised as a new node.

Step 2 uses lem-pc-kflat-resolution and lem-pur-kflat-total-tensor-model. The former permits any complex on any ringed site and supplies flat terms as well as K-flatness. The latter explicitly allows both complexes to be unbounded in both directions, gives their flat-term K-flat total tensor, the signed reassociation and its derived-tensor interpretation. No finite Tor dimension or flat cohomology assumption is being supplied silently. This repaired the earlier inline exact-coproduct argument by pointing to the exact existing result.

Step 3 uses lem-weil-pbc-ringed-topos-kflat-pullback, lem-weil-pbc-site-derived-tensor-descent, and lem-pur-kflat-change-of-rings. Their statements give, respectively, preservation of K-flat complexes with flat terms under an arbitrary ringed-topos pullback, computation of derived tensor through the localization of such representatives, and the scalar-extension specialization without a flat ring map. Apply the first on the small sequence site itself, not just at its levels. Apply the third to each actual R_T -> A_n. All hypotheses have been supplied by steps 1 and 2.

Step 4 cites def-pur-sheaf-tensor-product and def-pc-tensor-complex-sheaves for the sheafified balanced tensor and the signed direct-sum total differential. The remaining argument is elementary: the two displayed balanced formulas are inverse because coefficients can be moved across the A_n-balanced tensor; their differential signs coincide on degree (i,j); and multiplicativity and preservation of 1 prove commutation with every transition. This is an explicit calculation rather than an appeal to a source tag as a theorem. The coefficients have degree zero, so there is no missing Koszul sign in their multiplication. No flatness of A_n over R_T is used.

Step 5 uses lem-sfb-ringed-derived-monoidal-comparisons and lem-weil-pbc-site-derived-tensor-descent. The former states the canonical tensor isomorphism for arbitrary small ringed topoi and its monoidal coherence. The latter states the localization equivalence and extension/uniqueness of natural transformations on flat-term K-flat pairs. Together with the explicit step-4 comparison they provide naturality and representative independence on the whole system category. The canonical direction in the item is inverse to multiplication; balancing also identifies it with the usual scalar-extension convention placing a in the first factor. Evaluations alone would be insufficient to prove equality of arbitrary morphisms; the proof instead has an actual chain map on systems and a localization theorem.

Step 6 uses lem-coef-semilinear-derived-sections and lem-sfb-ringed-derived-monoidal-comparisons. The first states exact levelwise inverse image, its adjoint and simultaneous operations on the ringed topos of systems. The ordinary sheaf-system inverse image preserves finite limits componentwise and has levelwise geometric direct image as right adjoint. The constant-system comparison is identity at each level, and its structural ring maps are the same pulled-back completion projections. Thus the generic composition and ring-compatible 2-isomorphism clauses of the second cited statement apply. The statement's assumed canonical identifications g^{-1}R_T=R_T' and g^{-1}A_n,T=A_n,T' are used explicitly; no general commutation of inverse image with arbitrary inverse limits is claimed.

Step 7 uses lem-weil-pbc-ringed-topos-kflat-pullback and lem-coef-semilinear-derived-sections. These statements supply legitimate resolving pullbacks and the evaluation normalizations of simultaneous tensor/scalar operations. Under the coefficient identifications, geometric module pullback is inverse image, so the evaluated comparison is the ordinary inverse-image/scalar comparison on the chosen Q. Its transition formula is written out as g^{-1}(1 tensor h)=1 tensor g^{-1}(h). This proves the specified evaluation without replacing the original comparison by a family of unrelated isomorphisms.

Step 8 uses the associator, unit and monoidal composition/2-isomorphism clauses of lem-sfb-ringed-derived-monoidal-comparisons. The additional normalization checks are explicit: q maps to q tensor 1; both triple products multiply a,b,c in order; the unit multiplies by 1; and consecutive quotients preserve products. Pulling back applies the same ring operations. The resulting equations already hold on strict resolving systems, and the cited monoidal comparisons give the corresponding derived constraints. The step does not use any completeness, constructibility or boundedness result.

For small cases I checked the zero input, two degree-zero free rank-one inputs, the tensor unit, the identity geometric morphism and a repeated/identity quotient. The maps reduce respectively to zero, multiplication/insertion of 1, the usual unitors, the identity scalar comparison and the same multiplicative formula. I also checked the nonflat basic coefficient map Z_ell -> Z/ell: the proof resolves the source inputs and therefore does not mistake underived tensor of arbitrary objects for derived tensor. Arbitrarily unbounded inputs are covered by direct-sum totalization and the existing total-tensor theorem, not by a bounded-resolution argument.

Every non-elementary fact used in the steps has a node citation whose statement was read, with a verbatim quote in citations.json. Existing off-unit homological/topos lemmas are declared in split_report.tool_uses as generic tools; none replaces the unit route. All new-node form checks are vacuous because none was made. Every step is below 2000 characters, the proof-dependency list is the union of uses, and no proof claim is hidden in a newly introduced statement. No repository, launcher, Lean file or compiler was modified or run.

## Unfinished work

None in the stage-1 split. All further proofs remain the existing DAG nodes' own work; this delivery does not assert Lean closure of them. The remote dry run and push are executed by the prescribed delivery tool after this report is written.
