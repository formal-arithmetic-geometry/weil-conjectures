# Worker report

Item: lem-weil-pbc-ordered-exchange-coefficient-comparison. Group NZ. Stage 1 only. Human-requested re-split dated 2026-10-21.

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-ordered-exchange-coefficient-comparison.json: unchanged statement; five assembly steps, 2469 text characters.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-completed-scalar-unit-adjunction.json: statement, unsplit; no Mathlib match after two semantic phrasings, Loogle and source grep; no proof steps.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-flat-scalar-tower-exchange.json: statement, unsplit; no Mathlib match after two semantic phrasings, Loogle and source grep; no proof steps.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-flat-scalar-tower-limit-square.json: statement, unsplit; no Mathlib match after two semantic phrasings, Loogle and source grep; no proof steps.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-quotient-diagram-scalar-projection.json: statement, unsplit; no Mathlib match after two semantic phrasings, Loogle and source grep; no proof steps.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-strict-quotient-scalar-balancing.json: statement, unsplit; no Mathlib match after two semantic phrasings, Loogle and source grep; no proof steps.
- report.md and citations.json: argument allocation, source/statement review and verbatim citation evidence.

## Attachments

None. I searched lean/WeilConjectures for the item tag and ordered exchange/coefficient/diagonal notions. The actual module lean/Sheaf/Paper/OrderedExchangeCoefficientComparison.lean states the item but coefficientComparison ends in sorry; ordinaryRho_existsUnique, rho_existsUnique, lambda_existsUnique, phi_existsUnique, rho_unit, completedHom_normalization and normalized_naturality are also sorried. No finished project declaration gives the whole item or a whole new statement. No Lean was written, and no compiler or build was invoked.

## WANTED

None. The current blueprint and the ingredient Stacks source files are present.

## What changed and what was wrong

The statement was already reviewed and is retained byte for byte. The defect specified by the human was the size of its fourteen-step inline proof (15922 characters), not a statement dispute. I separated five mathematical comparison obligations, all status unsplit, proof=[], proof_deps=[], proof_origin=null. They have statements, not hidden proof sketches. The old proof is preserved verbatim below so its models, transposes and equality arguments remain available. The assembly now cites only statements that give the required equations.

The first duplicate audit found that the proposed diagonal/quotient-exchange extraction was already covered by lem-sbc-unbounded-exact-adjunction-square and lem-sbc-strict-quotient-exchange-unit-equation. I discarded that proposed node, kept its search log as research history, and cite the existing lemmas. I separated strict quotient balancing from scalar projection instead. This is the only change of split design; no mathematical argument was discarded.

No incompleteness remains in this stage-1 delivery beyond the intentionally statement-only child nodes.

## Allocation of every old argument

| Old step | Where the argument now belongs |
| --- | --- |
| 1 | Parent assembly step 1, using the existing flat-ringed-diagram theorem twice; its exact-left-adjoint justification is part of that cited theorem. |
| 2 | lem-weil-pbc-flat-scalar-tower-limit-square: arbitrary towers, compatible-family normalization, and the whole K-injective direct-image/limit square. |
| 3 | Existing lem-sbc-unbounded-exact-adjunction-square, especially clauses (1), (3), (4); no duplicate node created. |
| 4 | lem-weil-pbc-strict-quotient-scalar-balancing; parent step 2 assembles beta, delta and rho_M from its explicit comparisons. |
| 5 | lem-weil-pbc-quotient-diagram-scalar-projection: the actual adjunct-of-counit equation, on strict diagrams. |
| 6 | Existing lem-sbc-strict-quotient-exchange-unit-equation, whose statement gives invertible H,Hprime and v equal to the actual diagram mate; no duplicate node created. |
| 7 | lem-weil-pbc-flat-scalar-tower-exchange: arbitrary derived tower, coefficient-composition coherence, and the actual transpose formula. |
| 8 | Parent step 3, by the existing strict-tower witness normalization and ordered definition. |
| 9-10 | lem-weil-pbc-completed-scalar-unit-adjunction: quotient units, unique extension, fixed Hom bijections, units/counits and conjugates. |
| 11 | The same new lemma gives the general reconstruction identity and its naturality under a constant-input isomorphism; parent step 4 specializes to gprime,K and g,Rf_*K, using chi_f. |
| 12 | Parent step 5: source normalization is functorial substitution. |
| 13 | Parent step 5: substitute Z and the target reconstruction in the new arbitrary-tower scalar-limit square. |
| 14 | Parent step 5: functorial substitution and cancellation, and naturality on the full complete category. |

The new statements have sizes lem-weil-pbc-completed-scalar-unit-adjunction: 4358, lem-weil-pbc-flat-scalar-tower-exchange: 2320, lem-weil-pbc-flat-scalar-tower-limit-square: 2103, lem-weil-pbc-quotient-diagram-scalar-projection: 2577, lem-weil-pbc-strict-quotient-scalar-balancing: 2785 characters. They carry separate arguments: none restates the parent, asserts the ordered completed-exchange formula, or claims identity/pasting laws. The two existing generic results remove duplication rather than moving the work into a replacement catch-all.

## Review by NZ

I read GOAL.md, the three-level route in SETUP.md, the proper-base-change chapter and sk-thm-properbasechange unit, stages/1-dag.md, coord/brief-stage1.md and delivery-errors B through E. The current source is literature/blueprint/main-20261015/blueprint/sec-proper-base-change/sk-thm-properbasechange/lemma-weil-pbc-completed-exchange-coherence.proof.md, paragraph 2. It asks for the same reconstruction, projection-formula and direct-image/limit conjugations. The detailed coefficient argument is an agent supplement, already marked as such; neither that short paragraph nor a Stacks tag is falsely represented as stating this combined theorem. The chapter/unit route is unchanged.

I read Stacks proetale.tex, lemma-naive-completion (099M) and lemma-pushforward-Noetherian-case (099N), including their proofs; sites-cohomology.tex, lemma-Rf-commutes-with-Rlim (0A07), including its strict diagram-site proof and warning that Rlim is not an ordinary limit in the derived category; remark-compatible-with-diagram (0E48); and derived.tex, lemma-adjoint-preserve-K-injectives (08BJ). The projection map is the actual counit-tensor adjunct specified by def-weil-pbc-projection-formula-map, with its source equation 0B56. These are ingredients, not citations pretending the source states a scalar comparison it omits. Each new source.place says exactly which old supplementary argument it separates.

For flat-scalar-tower-limit-square I checked the two sites, the scalar maps, flatness, both coefficient inverse-image isomorphisms, and their commuting square. Its lambda is specified on all towers and by the actual compatible-family comparison and derived units. The target equation has source r_V R_u^S L_U^S Z and target L_V^R R_u^R,tower r_U Z along both routes. The exact left adjoint needed for restriction to preserve K-injectives is scalar extension; exact restriction alone would not justify that claim. The limit functor is right adjoint to exact Delta. Thus the common K-injective argument retained from old step 2 has every necessary exactness hypothesis. No exact-products hypothesis was inserted.

For strict-quotient-scalar-balancing I checked that the source is a single strict quotient diagram on the diagram site, not a family in D at the levels. The object, augmentation, transitions, rho and q are defined in the statement. Its equation compares q after restriction of pullback/reduction reassociation with reduction of the ambient scalar comparison after rho. Both end in G_u R_V^0 r_V L. I retained the quotient-unit equation needed later; the finite-reduction scalar node alone only states level comparisons, so it was not silently used for an equality of strict derived arrows.

For quotient-diagram-scalar-projection I read the actual definition of pi and the full flat diagram restriction theorem. The latter says restriction identifies adjuncts, not just objects, so the old counit-tensor transpose computation is a separate genuine obligation. The new statement requires the pi maps to be exactly these adjuncts and states their strict-derived equation. The rho and q named there are supplied by the balancing node, not chosen arbitrarily. Its proof remains for another worker; the original tensor section calculation and localization descent are preserved below. No general monoidal equivalence of the ambient coefficient categories is claimed.

For flat-scalar-tower-exchange I checked all four scalar squares and the agreement of the composite coefficient identifications. The statement supplies the actual pullback square, the canonical normalized p,d of flat diagram restriction, and the transpose of the transported mate. Its Z is arbitrary, so it is a reusable scalar-square lemma, not the parent coefficient-normalization conclusion at one reduction tower. The new source does not pretend 0E48 directly states this. The old sectionwise scalar multiplication/composition argument is retained below, as is the counit transpose.

For completed-scalar-unit-adjunction I read the complete-category equivalence, completed-pullback definition, Koszul reconstruction, the ringed Koszul reflector statement, and the constant completed-adjunction statement. The input is complete for quotient-unit invertibility, identified with Koszul completeness; the full subcategory and its unit precomposition bijection are essential. The new lemma states the unit equation on all ambient inputs, the unique extension phi, its explicit reconstruction equality, and equality of the prescribed Hom bijections. It retains the direct-image completeness check for intermediate inputs. Thus it has more substance than the existence of an equivalence, but makes no claim of an ambient equivalence. Its final naturality clause is exactly what permits chi_f at Rf_*K in the assembly.

Assembly step 1 uses the statement of profinite-coefficient-inverse-image for coefficient maps and composition; constant-completion-equivalence for flatness; flat-ringed-diagram-restriction for the actual ambient/tower p,d and adjuncts; and the new limit-square statement for lambda and its square. The scalar maps commute because on constant sections their quotient projections agree, and the ordinary limit universal property applies to coefficient sheaves. This argument is not an inference of equality of derived arrows from evaluations.

Assembly step 2 uses both new balancing and projection statements. I substituted their definitions to check beta and delta have the displayed directions. Pulling the single-edge projection equation by G_g and using the q equation gives precisely beta r(Ha)=H0 rho_M. No property of an unspecified isomorphism is being taken from a definition node.

Assembly step 3 uses the complete statement of lem-sbc-unbounded-exact-adjunction-square, especially its diagonal mate clause, and of lem-sbc-strict-quotient-exchange-unit-equation, especially its final assertion that v is the actual diagram mate. These are generic tools in another unit; the report and split_report declare that use. Its perfect-quotient hypothesis follows from the adic datum and the canonical flat coefficient identification; all coefficient pullbacks are isomorphisms. The new flat-scalar-tower-exchange equation then applies to this actual mate at R_Xa K. Naturality for rho gives the equation required. Only after that I invoke strict-tower-exchange-mate-normalization, whose properness and witnesses are checked in exactly the witnessed case, and the ordered completed-base-change definition. I checked the order c inverse, then L(v), then s, with H prime R(e) H inverse.

Assembly step 4 uses the completed-unit lemma, not the mere existence of an equivalence. Its displayed reconstruction equation is applied twice and naturality transports the source by chi_f. prop-weil-pbc-direct-image-limits explicitly says Rf_* preserves completeness, so the source input qualifies. The new lemma supplies Hom bijections, units, counits and conjugates, establishing all of clause (1).

Assembly step 5 is elementary functorial assembly from previous equations and the cited normalization square. I read prop-weil-pbc-direct-image-limits for its specified K-injective c, lem-sp-completion-mate-comparison for its exact H,s,t and their directions, and prop-weil-pbc-rlim-functoriality for applying the limit functor to strict-derived equations. Substituting c= kappa Rfprime(r) into the new square and using naturality of kappa and chi gives L(delta) lambda r(c)=t iota_T. Substituting s=L(H) r_S similarly gives the source equation. Then L(delta r(v))=L(E beta) and cancellation give the ordered formula. These are at most a few lines of functorial algebra, retained as assembly rather than a new lemma. Every map used is natural in all complete morphisms; completeness of completed pullback comes from its reflector description and completeness of direct image is checked explicitly.

I checked delivery-errors B-E against the actual node files. Every new node introduces all objects and assumptions, has statement-only unsplit shape, includes its definition/normalization dependencies, and retains single-escaped TeX after JSON decoding. Every parent citation has a verbatim statement in citations.json; whole statements are used where several clauses are needed. Definitions are not cited for unstated theorems. I checked that the two reused tools have no dependency path back to this item. No source route uses SGA. The five parent steps are all under 2000 characters, and their total is under 3000. The large new statement contexts contain no proof steps or hidden proof paragraphs.

For edge cases I checked K=0 (all maps uniquely zero), an empty scheme (zero module category), A=0, and I=A (completed coefficient ring zero and the full complete subcategory on the constant side is zero). For I=0 with A finite, the quotient towers are constant, rho and scalar comparisons are identities and the formulas reduce to ordinary mates. For A=Z, I=(ell), at a geometric point, rho is the usual balancing with Z/ell^n and lambda the same compatible-family map. I also checked non-complete ambient inputs in the balancing/projection/exchange lemmas, since those do not assume reconstruction is invertible. In the generic flat-scalar lemmas, R=S recovers the identity comparison; a nonflat coefficient extension would invalidate the K-injective reasoning, so flatness is retained explicitly. Identity and zero transitions do not affect any of the strict-diagram equations.

Corrections made during this reading: eliminated the duplicate diagonal/quotient-exchange candidate in favor of two existing lemmas; separated balancing from projection instead; repaired the dependency extraction for a bracket containing two node ids; recorded invalid Loogle NatIso as invalid and ran a valid replacement; recorded two rate-limited LeanSearch attempts as unavailable. I made no statement correction to the parent.

## Mathlib searches

All searches were run by /home/ubuntu/weil-launcher-all/batch2/msearch.py NZ lem-weil-pbc-ordered-exchange-coefficient-comparison and preserved in searches.jsonl, with full raw outputs in search-results/. Each new node records the exact tool/query and raw log record, including availability. I used two different semantic phrasings, Loogle and Mathlib grep for each candidate, including the new balancing candidate after the duplicate redesign. I read the hits: SheafOfModules.restrictScalars and the forgetful pushforward comparison in ChangeOfRings.lean / PushforwardContinuous.lean are ordinary, not these derived strict comparisons; AdicCompletion.ofTensorProduct_naturality concerns ordinary module completion; CategoryTheory.reflectorAdjunction is abstract and gives no quotient reconstruction; colimConstAdj/constLimAdj supply only abstract constant-diagram adjunctions; mateEquiv alone does not establish that the geometric coefficient/composition comparisons are the prescribed ones. No candidate is an exact theorem or one-line specialization of the full new statements. The parent search records from earlier work are preserved unchanged.

Blueprint searches included coefficient comparison, diagonal exchange, completion unit, scalar tower limit, quotient diagram, scalar tower exchange, completed scalar unit, completion adjunction, strict quotient balancing and scalar augmentation. I also scanned the whole DAG titles/statements and all matching-source-tag candidates. The nearest imported blueprint ancestor remains lemma-weil-pbc-completed-exchange-coherence; each new node records paragraph 2, its precise supplementary old steps, and via=[the item]. The broader same-tag statements are distinguished below.

## Not duplicates

- lem-weil-pbc-completed-scalar-unit-adjunction vs lem-weil-pbc-ordered-exchange-coefficient-comparison: existing node normalizes the entire ordered completed exchange at complete inputs; the new lemma isolates a smaller reusable comparison and has no ordered exchange conclusion.
- lem-weil-pbc-completed-scalar-unit-adjunction vs prop-weil-pbc-levelwise-truncations: existing node concerns normalized truncation towers and Tor conditions, not scalar balancing, counit-tensor projection or completed scalar adjunctions.
- lem-weil-pbc-completed-scalar-unit-adjunction vs det-prop-diagonal-tower-system: existing node constructs the projective-line diagonal cycle class and its torsion tower, not arbitrary strict scalar comparison maps.
- lem-weil-pbc-completed-scalar-unit-adjunction vs lem-sfb-adic-stratum-completion-unit: existing node restricts completion units to geometric strata and slices, not from completed to constant coefficient rings.
- lem-weil-pbc-completed-scalar-unit-adjunction vs lem-sfb-adic-complete-reduction-cone: existing node constructs normalized homotopy-limit cone legs and successor transpose maps, not the new strict scalar comparison or geometric completed adjunction.
- lem-weil-pbc-completed-scalar-unit-adjunction vs lem-sfb-adic-complete-residue-conservative: existing node detects isomorphisms of complete objects by their first residue; it gives no equality of the specified scalar/projection/unit transformations.
- lem-weil-pbc-completed-scalar-unit-adjunction vs lem-weil-pbc-completed-koszul-quotient-roos-augmentation: existing node compares Koszul and quotient Roos augmentations over one completed ring; it makes no completed-to-constant scalar change.
- lem-weil-pbc-completed-scalar-unit-adjunction vs def-weil-pbc-completed-quotient-ordinary-unit: existing node defines the ordinary quotient-limit unit; it states no scalar comparison theorem.
- lem-weil-pbc-completed-scalar-unit-adjunction vs lem-derived-exact-equivalence-squares: existing node assumes additive equivalences of whole ambient abelian categories; restriction here is only an equivalence on full derived-complete subcategories.
- lem-weil-pbc-completed-scalar-unit-adjunction vs def-weil-pbc-completed-quotient-completion-unit: existing node defines the actual quotient completion unit and augmentation; it states no scalar transport or adjunction compatibility.
- lem-weil-pbc-completed-scalar-unit-adjunction vs lem-weil-pbc-levelwise-isomorphism-cones: existing node detects strict tower isomorphisms and complete-object isomorphisms, not equality of scalar/projection maps.
- lem-weil-pbc-completed-scalar-unit-adjunction vs lem-weil-pbc-koszul-localization-assembly: existing node extends invertibility/equality through a localization using supplied normalization data; it supplies none of the scalar quotient or geometric adjunction comparisons.
- lem-weil-pbc-flat-scalar-tower-exchange vs lem-weil-pbc-ordered-exchange-coefficient-comparison: existing node normalizes the entire ordered completed exchange at complete inputs; the new lemma isolates a smaller reusable comparison and has no ordered exchange conclusion.
- lem-weil-pbc-flat-scalar-tower-exchange vs lem-sbc-strict-quotient-exchange-unit-equation: existing node identifies the strict quotient exchange with Hprime R(e) H inverse and gives a coaugmentation equation for one ring system; the new scalar-mate theorem compares two flat-related ring systems at arbitrary towers.
- lem-weil-pbc-flat-scalar-tower-exchange vs lem-sf-constant-semilinear-generator-comparison: existing node compares DVR semilinear generators under proper/open and bounded normalized constructible witness hypotheses; it does not cover an arbitrary flat scalar square on arbitrary strict towers.
- lem-weil-pbc-flat-scalar-tower-exchange vs lem-sf-generator-reduction-coherence: existing node compares bounded witnessed semilinear system generators at DVR coefficients; it has no arbitrary flat coefficient maps or arbitrary strict tower scalar-mate equation.
- lem-weil-pbc-flat-scalar-tower-exchange vs lem-weil-pbc-completed-reduction-pullback-square: existing node compares integral and finite-level inverse-image squares; it neither changes to constant ambient coefficients nor transports direct-image mates on arbitrary towers.
- lem-weil-pbc-flat-scalar-tower-exchange vs lem-weil-pbc-ringed-square-tensor-compatibility: existing node compares tensor constraints on supplied representative inputs for one ringed square, explicitly not exchange or adjunction mates.
- lem-weil-pbc-flat-scalar-tower-exchange vs lem-weil-pbc-ringed-exchange-tensor-coherence: existing node compares exchange with tensor/projection for one ringed square; it states no scalar-change identification of the two diagram mates.
- lem-weil-pbc-flat-scalar-tower-exchange vs lemma-weil-pbc-completed-exchange-coherence: existing node asserts identity and pasting for completed exchange, not the scalar comparison sublemma, and depends upward on this item.
- lem-weil-pbc-flat-scalar-tower-exchange vs lem-weil-pbc-finite-reduction-pullback-coherence: existing node compares integral and finite reduction pullback squares at a fixed quotient, not flat scalar transport of the strict direct-image mate.
- lem-weil-pbc-flat-scalar-tower-exchange vs lem-weil-pbc-finite-reduction-pullback-square: existing node is the fixed-level reduction inverse-image square, not arbitrary-tower scalar restriction and derived exchange.
- lem-weil-pbc-flat-scalar-tower-exchange vs lem-weil-pbc-finite-level-rectangle: existing node is an equality at each finite quotient only; it does not identify whole derived strict-tower mates under scalar change.
- lem-weil-pbc-flat-scalar-tower-exchange vs def-weil-pbc-ringed-tensor-square-presentation: existing node defines the ordinary tensor-square representative data and explicitly assumes no derived-square tensor coherence; it is not a scalar-mate theorem.
- lem-weil-pbc-flat-scalar-tower-limit-square vs lem-weil-pbc-ordered-exchange-coefficient-comparison: existing node normalizes the entire ordered completed exchange at complete inputs; the new lemma isolates a smaller reusable comparison and has no ordered exchange conclusion.
- lem-weil-pbc-flat-scalar-tower-limit-square vs lem-sbc-unbounded-exact-adjunction-square: existing node identifies diagonal/evaluation adjunctions for a single coefficient ring; it has no scalar-change versus arbitrary strict-limit square.
- lem-weil-pbc-flat-scalar-tower-limit-square vs lem-trf-proetale-unit-leray-chain-formula: existing node identifies a global-cohomology chain representative with a Leray unit; it has neither scalar change nor inverse limits.
- lem-weil-pbc-flat-scalar-tower-limit-square vs lem-weil-pbc-termwise-adjunction-homotopy: existing node derives the termwise homotopy-category adjunction, not an arbitrary-tower scalar/limit normalization.
- lem-weil-pbc-flat-scalar-tower-limit-square vs lem-weil-pbc-qcqs-higher-direct-image: existing node describes etale higher direct-image sheaves under qcqs hypotheses; it does not compare two coefficient systems or strict limits.
- lem-weil-pbc-flat-scalar-tower-limit-square vs lem-weil-pbc-right-adjoint-preserves-kinjective: existing node gives K-injective preservation only; it does not construct or equate the specified scalar/limit comparisons.
- lem-weil-pbc-flat-scalar-tower-limit-square vs lem-exc-proetale-derived-open-restriction: existing node compares direct image with restriction to a geometric open; it makes no change of coefficient ring or arbitrary strict-limit square.
- lem-weil-pbc-flat-scalar-tower-limit-square vs lem-sp-exact-pullback-derived-adjunction: existing node gives the derived Hom bijection for one exact module pullback, not its scalar/limit compatibility.
- lem-weil-pbc-flat-scalar-tower-limit-square vs lem-pd-section-derived-pushpull-normalization: existing node changes internal versus sectionwise module encodings by an ambient equivalence; it has no flat ring change or strict-limit normalization square.
- lem-weil-pbc-flat-scalar-tower-limit-square vs lem-weil-pbc-kinjective-pullback-abutment: existing node computes a cohomological abutment map from K-injective representatives; no scalar change or strict towers occur.
- lem-weil-pbc-flat-scalar-tower-limit-square vs lem-weil-pbc-kinjective-unit-leray: existing node computes the unit/Leray chain arrow on global sections, without a coefficient change or inverse-limit square.
- lem-weil-pbc-flat-scalar-tower-limit-square vs lem-weil-pbc-direct-image-roos-normalization: existing node compares Roos triangles for one coefficient ring assuming exact products; it has no scalar-change normalization and the new limit lemma assumes no exact products.
- lem-weil-pbc-quotient-diagram-scalar-projection vs lem-weil-pbc-ordered-exchange-coefficient-comparison: existing node normalizes the entire ordered completed exchange at complete inputs; the new lemma isolates a smaller reusable comparison and has no ordered exchange conclusion.
- lem-weil-pbc-quotient-diagram-scalar-projection vs prop-weil-pbc-levelwise-truncations: existing node concerns normalized truncation towers and Tor conditions, not scalar balancing, counit-tensor projection or completed scalar adjunctions.
- lem-weil-pbc-quotient-diagram-scalar-projection vs det-prop-diagonal-tower-system: existing node constructs the projective-line diagonal cycle class and its torsion tower, not arbitrary strict scalar comparison maps.
- lem-weil-pbc-quotient-diagram-scalar-projection vs lem-sfb-adic-stratum-completion-unit: existing node restricts completion units to geometric strata and slices, not from completed to constant coefficient rings.
- lem-weil-pbc-quotient-diagram-scalar-projection vs lem-sfb-adic-complete-reduction-cone: existing node constructs normalized homotopy-limit cone legs and successor transpose maps, not the new strict scalar comparison or geometric completed adjunction.
- lem-weil-pbc-quotient-diagram-scalar-projection vs lem-sfb-adic-complete-residue-conservative: existing node detects isomorphisms of complete objects by their first residue; it gives no equality of the specified scalar/projection/unit transformations.
- lem-weil-pbc-quotient-diagram-scalar-projection vs lem-weil-pbc-completed-koszul-quotient-roos-augmentation: existing node compares Koszul and quotient Roos augmentations over one completed ring; it makes no completed-to-constant scalar change.
- lem-weil-pbc-quotient-diagram-scalar-projection vs def-weil-pbc-completed-quotient-ordinary-unit: existing node defines the ordinary quotient-limit unit; it states no scalar comparison theorem.
- lem-weil-pbc-quotient-diagram-scalar-projection vs lem-derived-exact-equivalence-squares: existing node assumes additive equivalences of whole ambient abelian categories; restriction here is only an equivalence on full derived-complete subcategories.
- lem-weil-pbc-quotient-diagram-scalar-projection vs def-weil-pbc-completed-quotient-completion-unit: existing node defines the actual quotient completion unit and augmentation; it states no scalar transport or adjunction compatibility.
- lem-weil-pbc-quotient-diagram-scalar-projection vs lem-weil-pbc-levelwise-isomorphism-cones: existing node detects strict tower isomorphisms and complete-object isomorphisms, not equality of scalar/projection maps.
- lem-weil-pbc-quotient-diagram-scalar-projection vs lem-weil-pbc-koszul-localization-assembly: existing node extends invertibility/equality through a localization using supplied normalization data; it supplies none of the scalar quotient or geometric adjunction comparisons.
- lem-weil-pbc-strict-quotient-scalar-balancing vs lem-weil-pbc-ordered-exchange-coefficient-comparison: existing node normalizes the entire ordered completed exchange at complete inputs; the new lemma isolates a smaller reusable comparison and has no ordered exchange conclusion.
- lem-weil-pbc-strict-quotient-scalar-balancing vs prop-weil-pbc-levelwise-truncations: existing node concerns normalized truncation towers and Tor conditions, not scalar balancing, counit-tensor projection or completed scalar adjunctions.
- lem-weil-pbc-strict-quotient-scalar-balancing vs det-prop-diagonal-tower-system: existing node constructs the projective-line diagonal cycle class and its torsion tower, not arbitrary strict scalar comparison maps.
- lem-weil-pbc-strict-quotient-scalar-balancing vs lem-sfb-adic-stratum-completion-unit: existing node restricts completion units to geometric strata and slices, not from completed to constant coefficient rings.
- lem-weil-pbc-strict-quotient-scalar-balancing vs lem-sfb-adic-complete-reduction-cone: existing node constructs normalized homotopy-limit cone legs and successor transpose maps, not the new strict scalar comparison or geometric completed adjunction.
- lem-weil-pbc-strict-quotient-scalar-balancing vs lem-sfb-adic-complete-residue-conservative: existing node detects isomorphisms of complete objects by their first residue; it gives no equality of the specified scalar/projection/unit transformations.
- lem-weil-pbc-strict-quotient-scalar-balancing vs lem-weil-pbc-completed-koszul-quotient-roos-augmentation: existing node compares Koszul and quotient Roos augmentations over one completed ring; it makes no completed-to-constant scalar change.
- lem-weil-pbc-strict-quotient-scalar-balancing vs def-weil-pbc-completed-quotient-ordinary-unit: existing node defines the ordinary quotient-limit unit; it states no scalar comparison theorem.
- lem-weil-pbc-strict-quotient-scalar-balancing vs lem-derived-exact-equivalence-squares: existing node assumes additive equivalences of whole ambient abelian categories; restriction here is only an equivalence on full derived-complete subcategories.
- lem-weil-pbc-strict-quotient-scalar-balancing vs def-weil-pbc-completed-quotient-completion-unit: existing node defines the actual quotient completion unit and augmentation; it states no scalar transport or adjunction compatibility.
- lem-weil-pbc-strict-quotient-scalar-balancing vs lem-weil-pbc-levelwise-isomorphism-cones: existing node detects strict tower isomorphisms and complete-object isomorphisms, not equality of scalar/projection maps.
- lem-weil-pbc-strict-quotient-scalar-balancing vs lem-weil-pbc-koszul-localization-assembly: existing node extends invertibility/equality through a localization using supplied normalization data; it supplies none of the scalar quotient or geometric adjunction comparisons.

In addition to the tag-triggered comparisons: flat-ringed-diagram-restriction supplies single-edge pull/push adjunct comparisons, but not the strict quotient/projection equation or the four-edge pullback-composition equation. constant-completion-equivalence supplies finite reductions and quotient-completion compatibility, but not the actual strict-diagram balancing/pullback equation or completed geometric Hom comparison. ringed-projection-restriction concerns localization to a site slice, not coefficient restriction. constant-tower-pushforward-normalization supplies the diagonal comparison and its counit, and is reused through the exact-adjunction-square tool. realization-adjoint-comparisons and realization-completed-mate concern bounded constructible DVR rational realization with properness, not these arbitrary inputs and flat coefficient systems. flat-restriction-derived-mate is the one-edge derived scalar comparison with a universal-unit equation, not the four-edge exchange-mate transport. The two generic diagonal/quotient tools found during the audit are cited, not recreated.


Additional same-tag comparisons requested by the first dry run (server ordering differs from the read mirror):

- lem-weil-pbc-completed-scalar-unit-adjunction vs def-derived-cochain-comparison-factors: existing node defines standard cochain/homotopy localization factors for an additive functor, with no scalar, quotient, projection, or completed geometric-adjunction assertion.
- lem-weil-pbc-completed-scalar-unit-adjunction vs def-derived-cochain-counit: existing node defines a cochain-localized left-derived comparison from supplied data, with no existence or coefficient-compatibility theorem.
- lem-weil-pbc-completed-scalar-unit-adjunction vs def-derived-cochain-right-unit: existing node defines a cochain-localized right-derived comparison from supplied data, with no strict quotient/scalar or geometric completed-adjunction equality.
- lem-weil-pbc-completed-scalar-unit-adjunction vs def-derived-exact-equivalence-square-data: existing node defines supplied compatible comparison data assuming ambient abelian equivalences, whereas completed-to-constant restriction is not an ambient equivalence.
- lem-weil-pbc-completed-scalar-unit-adjunction vs def-weil-pbc-adic-coefficient-datum: existing node defines the single completed-coefficient strict reduction tower, but gives no comparison with the constant-coefficient reduction or its geometric projection/adjunction normalization.
- lem-weil-pbc-completed-scalar-unit-adjunction vs def-weil-pbc-completed-constant-presentation-data: existing node defines compatibility fields for a chosen completed-coefficient presentation without an existence assertion; it has no geometric pullback or projection compatibility conclusion.
- lem-weil-pbc-completed-scalar-unit-adjunction vs def-weil-pbc-intrinsic-completion: existing node defines Koszul completion and its unit over a single completed ring, without changing to constant coefficients or proving the new strict comparison equations.
- lem-weil-pbc-completed-scalar-unit-adjunction vs lem-constant-completion-unit-normalization: existing node compares a specified constant completion-unit presentation with its cochain model; it does not construct the strict balancing/pullback comparison, compare geometric projection adjuncts, or identify the completed Hom bijections.
- lem-weil-pbc-quotient-diagram-scalar-projection vs def-derived-cochain-comparison-factors: existing node defines standard cochain/homotopy localization factors for an additive functor, with no scalar, quotient, projection, or completed geometric-adjunction assertion.
- lem-weil-pbc-quotient-diagram-scalar-projection vs def-derived-cochain-counit: existing node defines a cochain-localized left-derived comparison from supplied data, with no existence or coefficient-compatibility theorem.
- lem-weil-pbc-quotient-diagram-scalar-projection vs def-derived-cochain-right-unit: existing node defines a cochain-localized right-derived comparison from supplied data, with no strict quotient/scalar or geometric completed-adjunction equality.
- lem-weil-pbc-quotient-diagram-scalar-projection vs def-derived-exact-equivalence-square-data: existing node defines supplied compatible comparison data assuming ambient abelian equivalences, whereas completed-to-constant restriction is not an ambient equivalence.
- lem-weil-pbc-quotient-diagram-scalar-projection vs def-weil-pbc-adic-coefficient-datum: existing node defines the single completed-coefficient strict reduction tower, but gives no comparison with the constant-coefficient reduction or its geometric projection/adjunction normalization.
- lem-weil-pbc-quotient-diagram-scalar-projection vs def-weil-pbc-completed-constant-presentation-data: existing node defines compatibility fields for a chosen completed-coefficient presentation without an existence assertion; it has no geometric pullback or projection compatibility conclusion.
- lem-weil-pbc-quotient-diagram-scalar-projection vs def-weil-pbc-intrinsic-completion: existing node defines Koszul completion and its unit over a single completed ring, without changing to constant coefficients or proving the new strict comparison equations.
- lem-weil-pbc-quotient-diagram-scalar-projection vs lem-constant-completion-unit-normalization: existing node compares a specified constant completion-unit presentation with its cochain model; it does not construct the strict balancing/pullback comparison, compare geometric projection adjuncts, or identify the completed Hom bijections.
- lem-weil-pbc-strict-quotient-scalar-balancing vs def-derived-cochain-comparison-factors: existing node defines standard cochain/homotopy localization factors for an additive functor, with no scalar, quotient, projection, or completed geometric-adjunction assertion.
- lem-weil-pbc-strict-quotient-scalar-balancing vs def-derived-cochain-counit: existing node defines a cochain-localized left-derived comparison from supplied data, with no existence or coefficient-compatibility theorem.
- lem-weil-pbc-strict-quotient-scalar-balancing vs def-derived-cochain-right-unit: existing node defines a cochain-localized right-derived comparison from supplied data, with no strict quotient/scalar or geometric completed-adjunction equality.
- lem-weil-pbc-strict-quotient-scalar-balancing vs def-derived-exact-equivalence-square-data: existing node defines supplied compatible comparison data assuming ambient abelian equivalences, whereas completed-to-constant restriction is not an ambient equivalence.
- lem-weil-pbc-strict-quotient-scalar-balancing vs def-weil-pbc-adic-coefficient-datum: existing node defines the single completed-coefficient strict reduction tower, but gives no comparison with the constant-coefficient reduction or its geometric projection/adjunction normalization.
- lem-weil-pbc-strict-quotient-scalar-balancing vs def-weil-pbc-completed-constant-presentation-data: existing node defines compatibility fields for a chosen completed-coefficient presentation without an existence assertion; it has no geometric pullback or projection compatibility conclusion.
- lem-weil-pbc-strict-quotient-scalar-balancing vs def-weil-pbc-intrinsic-completion: existing node defines Koszul completion and its unit over a single completed ring, without changing to constant coefficients or proving the new strict comparison equations.
- lem-weil-pbc-strict-quotient-scalar-balancing vs lem-constant-completion-unit-normalization: existing node compares a specified constant completion-unit presentation with its cochain model; it does not construct the strict balancing/pullback comparison, compare geometric projection adjuncts, or identify the completed Hom bijections.
- lem-weil-pbc-flat-scalar-tower-exchange vs lem-weil-pbc-intrinsic-finite-exchange-rectangle: existing node compares integral and finite quotient exchange at a fixed n; the new statement compares flat-related ring systems on every arbitrary derived strict tower and includes the composite pullback normalization.
- lem-weil-pbc-flat-scalar-tower-limit-square vs lem-weil-pbc-constant-tower-pushforward-normalization: existing node fixes direct image and limit on constant towers for one coefficient ring; the new statement is an arbitrary-tower comparison square involving a separate flat scalar restriction.

Dry-run repair: the first run stopped at the report duplicate check; I read all ten additional cited statements, added the distinctions above and corrected the projection node source pointer from old Steps 4-5 to old Step 5. The parent statement is unchanged.

## Preserved argument text for subsequent workers

The following is the exact original proof text, kept outside the new statement-only nodes. It records the intended proofs of their obligations and the short assembly; its correctness is checked above. It is research/delivery guidance, not a second proof field or a claim the new nodes are already split.

### Original step 1

Write $r_T=\operatorname{Res}_T$, and distinguish the one-object indexing category from $J=\mathbf N_{\geq1}^{op}$. The coefficient maps commute with $\underline A\to A_T$: on constant sections both composites send $a$ to its image, and the finite projections determine the map to $A_U$. The profinite inverse-image lemma supplies both the coefficient isomorphisms and their composition/transition compatibility. Flatness of $A_T$ over $\underline A_T$ is supplied by the constant-completion equivalence. Apply the flat ringed diagram restriction theorem first with the one-object category and then with $J$. All sites are small; its scalar-square and flatness hypotheses have just been checked. In the first application it gives $a_u:r_ULu_a^*\simeq G_ur_V$ and $\chi_u:r_VRu_*\simeq R_u^0r_U$ on AMBIENT module complexes, with the stated adjunct compatibility. In the second it gives $p_u:r_U\mathscr L_u\simeq G_ur_V$ and $d_u:r_V\mathscr R_u\simeq R_u^{\mathcal T}r_U$. These use the identified underlying inverse image and direct image on a K-injective model. Explicitly the left adjoint of restriction is $A_T\otimes_{\underline A_T}-$, exact by flatness; the right-adjoint K-injective theorem applies for this reason, not merely because restriction itself is exact.

Cited nodes: lem-weil-pbc-profinite-coefficient-inverse-image, lem-weil-pbc-constant-completion-equivalence, lem-weil-pbc-flat-ringed-diagram-restriction, lem-weil-pbc-right-adjoint-preserves-kinjective.

### Original step 2

For an ARBITRARY completed-coefficient tower $Z$, apply the ringed tower pushforward/limit comparison to the identity geometric morphism with structure map $\underline A_T\to A_T$. Its module direct image is restriction; restriction is exact, so its derived functor is $r_T$. This gives $\lambda_Z:r_T\mathcal L^aZ\simeq\mathcal Lr_TZ$, without a finite-reduction hypothesis. Check its normalization together with direct image as follows. Choose a K-injective tower $Z\to J_Z$; such resolutions exist since the small module diagram categories are Grothendieck. Restriction preserves its K-injectivity by Step 1. Also $\lim J_Z$ is K-injective: $\lim$ is right adjoint to the exact constant-diagram functor, so the right-adjoint theorem applies. For each edge the ordinary and diagram direct images preserve K-injectives, since their identified inverse images are exact. Thus $J_Z,rJ_Z,u_*J_Z,\lim J_Z$ compute the required derived composites. Denote their direct-image/limit comparisons by $\kappa_u^a,\kappa_u^0$. On these models the two routes below are the SAME equality of complexes, $r_Vu_*\lim J_Z=\lim u_*r_UJ_Z$:
$$\mathcal L(d_{u,Z})\lambda_{\mathscr R_uZ}r_V(\kappa_u^a(Z))=\kappa_u^0(r_UZ)R_u^0(\lambda_Z)\chi_{u,\mathcal L^aZ}.$$
The K-injective total-derived theorem identifies these models with the canonical derived functors. This proves compatibility of the specified comparisons, not uniqueness from their finite projections.

Cited nodes: lem-weil-ringed-tower-pushforward-limit-comparison, lem-weil-pbc-small-module-diagrams-grothendieck, lem-weil-pbc-kinjective-functorial-existence, lem-weil-pbc-right-adjoint-preserves-kinjective, lem-weil-pbc-kinjective-total-derived, lem-weil-pbc-flat-ringed-diagram-restriction.

### Original step 3

The diagram-site realization identifies strict towers with modules on one small ringed site, with ring $\Delta A_T$. For this $J$, object $1$ is terminal, so $\operatorname{colim}_J=\operatorname{ev}_1$ is exact. Its right adjoint $\Delta$ therefore preserves K-injectives by the right-adjoint theorem. An ambient K-injective representative $I_K$ consequently computes $\mathscr R_f\Delta K=\Delta Rf_*K$ by the same complex $\Delta f_*I_K$; the same argument applies to $f'$ and any ambient input $E$. A diagonal flat-term K-flat representative is K-flat on the diagram site: its tensor with an acyclic diagram is acyclic at every level, hence acyclic by levelwise cohomology. Existence of the ambient representative and the derived tensor comparison are supplied by the K-flat resolution and tensor-descent nodes. On these representatives the diagonal adjunction bijections are the componentwise ordinary ones. The characterization of the derived bijection on fraction representatives therefore identifies diagonal units and counits with the ambient ones. Pullback composition is termwise as well. By the mate's transpose formula the diagram exchange on $\Delta K$ is $\Delta e$. This comparison uses no properness or finite-origin witnesses.

Cited nodes: lem-weil-pbc-diagram-site-realization, lem-weil-pbc-right-adjoint-preserves-kinjective, lem-weil-pbc-kinjective-total-derived, lem-pc-kflat-resolution, lem-weil-pbc-site-derived-tensor-descent, lem-weil-tower-category-levelwise-abelian, lem-pc-pre-derived-adjoint-functors-general, def-weil-pbc-adjunction-mate.

### Original step 4

On the diagram site, the constant-completion equivalence applies to $\Delta\underline A_T\to\Delta A_T$: constant sheaves and limits are fiberwise under the diagram-site equivalence. Apply its finite-reduction comparison to $\Delta K$. The strict tensor construction gives
$$\rho_K:r_X\mathcal R_X^aK\simeq\mathcal R_X\bar K.$$
On a flat-term K-flat representative $P$, both sides are the SAME quotient diagram $(P/I^nP)_n$ with its quotient transitions; the map sends the class of $p$ to itself. Thus it respects the quotient unit as well. The derived tensor/pullback comparison and the coefficient identities identify $\mathcal R_U^aLu_a^*L$ with $\mathscr L_u\mathcal R_V^aL$. Combining this with $p_u$ and the preceding balancing map gives $\rho_{u,L}:r_U\mathscr L_u\mathcal R_V^aL\simeq G_u\mathcal R_Vr_VL$. These are strict-diagram comparisons, natural in $L$. Define
$$\beta=(G_gR_f^{\mathcal T}\rho_K)(G_gd_f)p_g,\qquad
\delta=(R_{f'}^{\mathcal T}G_{g'}\rho_K)(R_{f'}^{\mathcal T}p_{g'})d_{f'}.$$
Finally $\rho_M$ is the same reduction comparison for $M$, followed by $\mathcal R(a_g)$ and $\mathcal R(G_g\chi_f)$. These formulas give exactly the source, target and coefficient identifications specified in (2).

Cited nodes: lem-weil-pbc-diagram-site-realization, lem-weil-pbc-constant-completion-equivalence, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-flat-ringed-diagram-restriction.

### Original step 5

Check the projection-formula equation by transposition, rather than by evaluations. On each coefficient diagram the projection map is the adjunct of $(\varepsilon_{f,K}\otimes1)t_f$. The adjunct clause of flat diagram restriction identifies its restricted adjunct with the adjunct of its restricted transpose, and in particular identifies the restricted counit with the constant-coefficient counit. Under $\rho$, the tensor factor in that transpose is a quotient: on a K-flat representative the comparison is $p\otimes\bar a\mapsto p\otimes\bar a$, and the pullback/tensor comparison sends it to $(p\otimes1)\otimes\bar a$. Applying a morphism $h$ before or after either map sends it to $(h(p)\otimes1)\otimes\bar a$. Use this with the counit and the identified pullback. Hence the restricted transpose is exactly $(\varepsilon^0_{f,\bar K}\otimes1)t_f^0$. Bijectivity of the adjunct correspondence identifies the two projection maps. Apply $G_g$ and use the formulas for $\beta,\rho_M$ in Step 4 to obtain
$$\beta\,r(H^a)=H^0\rho_M.$$
This is an equality of derived diagram morphisms: the tensor comparisons come from natural maps on the resolving class, and tensor descent makes their equality an equality after localization. No general monoidal identification of the two ambient scalar categories is used.

Cited nodes: def-weil-pbc-projection-formula-map, lem-weil-pbc-flat-ringed-diagram-restriction, lem-weil-pbc-constant-completion-equivalence, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-site-derived-tensor-descent.

### Original step 6

Let $W$ be the completed-coefficient strict-diagram exchange at $\mathcal R_X^aK$, defined by its adjunction mate. Apply ringed exchange/tensor coherence on the completed ringed diagram sites with object $\Delta K$ and coefficient object $Q_{Y,\bullet}=(\underline{P_n}_Y)_n$. This theorem allows arbitrary ringed topoi and needs no properness. The coefficient isomorphisms give $\mathscr L_uQ_{V,\bullet}\simeq Q_{U,\bullet}$, respecting the full quotient diagram and the square. Step 3 identifies exchange at $\Delta K$ with $\Delta e$. Thus the first composite in the coherence theorem is $WH^a$, while the second is $H'^a\mathcal R_{Y'}^a(e)$. Its stated equality gives
$$WH^a=H'^a\mathcal R_{Y'}^a(e),\qquad W=v^a.$$
Here right composition with the specified inverse of $H^a$ gives the second equation. The inverses in the item exist: their evaluations are perfect projection-formula isomorphisms; their cones have zero evaluated cohomology and hence zero cohomology diagram. This uses conservativity for isomorphisms from levelwise exactness, never faithfulness of evaluations on morphisms.

Cited nodes: lem-weil-pbc-ringed-exchange-tensor-coherence, lem-weil-pbc-profinite-coefficient-inverse-image, def-weil-pbc-strict-tower-operations, lemma-weil-pbc-perfect-projection-formula, lem-weil-tower-category-levelwise-abelian, lem-weil-ringed-tower-pushforward-limit-comparison.

### Original step 7

Before composing with $\rho_K$, let $b,d$ be the two composites of $p_u,d_u$ for the corners at $r_X\mathcal R_X^aK$. Transpose $d\,r(W)b^{-1}$ under $G_{f'}\dashv R_{f'}^{\mathcal T}$. The adjunct clause of flat diagram restriction replaces its counit by the constant-coefficient counit. Pullback composition is also identified: its K-flat representative multiplies nested extension scalars, and after restriction both routes are the same composite inverse-image identification; the coefficient composition compatibility identifies their ring actions. Consequently its transpose is
$$G_{g'}\varepsilon_f^{\mathcal T}\circ\theta^{\mathcal T}_{\square,R_f^{\mathcal T}r_X\mathcal R_X^aK}.$$
This is precisely the transpose defining $E^{\mathcal T}_{r_X\mathcal R_X^aK}$. The adjunction bijection gives $d\,r(W)=E^{\mathcal T}b$. Compose with $R_{f'}^{\mathcal T}G_{g'}\rho_K$ and use naturality of this mate for $\rho_K$; with Step 6 and the definitions of $\beta,\delta$ this is
$$\delta\,r(v^a)=E^{\mathcal T}_{\mathcal R_X\bar K}\beta.$$
All equalities are in the derived strict-diagram category and hold for every complete $K$.

Cited nodes: lem-weil-pbc-flat-ringed-diagram-restriction, lem-weil-pbc-proetale-derived-pullback-composition, lem-weil-pbc-profinite-coefficient-inverse-image, def-weil-pbc-adjunction-mate, def-weil-pbc-strict-tower-operations.

### Original step 8

Only now assume the additional properness and the levelwise etale-origin witnesses in the strict-tower exchange normalization lemma. Its statement specifies $B_\bullet,D_\bullet$ as precisely $B^a,D^a$ and $v'_\bullet=H'^a\mathcal R^a(e)(H^a)^{-1}=v^a$. Its $b,d$ are normalized by the same restricted inverse images and the same K-injective direct images as Step 1. Therefore the $\beta,\delta$ of Step 4 are those $b,d$ followed by the images of $\rho_K$. The ordered completed base-change definition has source map $\mathcal L^a(H^a)r_S=s^a$, tower map $v^a$, and target comparison $c^a$ with the same direction. Substitution gives exactly $x^a_K=(c^a)^{-1}\mathcal L^a(v^a)s^a$. Since this expression was constructed before witnesses, it is independent of which witnesses are supplied. No assertion of that lemma was applied to an unwitnessed input.

Cited nodes: lem-weil-pbc-strict-tower-exchange-mate-normalization, def-weil-pbc-completed-base-change-map.

### Original step 9

We fix the completed comparison by its unit. Let $L$ be complete on $V$, and put $j^a_{u,L}:Lu_a^*L\to F_u^aL$. By the completed-pullback definition and Koszul reconstruction, this is quotient completion, with its canonical unit. The constant-completion equivalence identifies this unit with the constant coefficient completion unit. With the strict pullback/reduction comparison of Step 4 and $\lambda$ of Step 2, set
$$\Psi_{u,L}=\mathcal L(\rho_{u,L})\lambda\,r_U(r_{u,L}):r_UF_u^aL\longrightarrow\mathcal L G_u\mathcal R_Vr_VL=F_u^0r_VL.$$
Here $r_{u,L}$ is the defining reconstruction into $\mathcal L^a\mathscr L_u\mathcal R_V^aL$. All factors are isomorphisms. The two maps out of the uncompleted pullback satisfy
$$\Psi_{u,L}\,r_U(j^a_{u,L})=j^0_{u,r_VL}\,a_{u,L}.$$
Indeed they arise from the identical strict map from the constant representative to its quotient diagram: Step 4 sends $p$ to its same class at every level WITH its transitions, and Step 2 takes the same limit after restriction. Thus this is equality of induced completion-unit maps, not an argument from evaluated equalities. The reflector node supplies bijectivity of precomposition with this unit for maps into any complete object; Koszul reconstruction identifies its unit with the quotient unit being used.

Cited nodes: def-weil-pbc-completed-pullback, prop-weil-pbc-koszul-reconstruction, lem-weil-pbc-constant-completion-equivalence, lem-weil-pbc-ringed-koszul-completion-reflector, lem-sp-completed-pullback-adjunction.

### Original step 10

The unit identity in Step 9 identifies $\Psi_{u,L}$ with the stipulated $\phi_{u,L}$, as follows. For complete $N$ on $U$, the two completed-adjunction Hom bijections first precompose with $j^a_{u,L}$ or $j^0_{u,r_VL}$ and then use the ambient adjunction. Step 1's adjunct clause says the second operations agree under $a_u,\chi_u$; Step 9's identity says the first operations agree under $\Psi_u$. Equivalences on complete objects are fully faithful by constant-completion equivalence. Hence $\Psi_u$ respects exactly these Hom bijections and is the isomorphism defining $\phi_u$ in (1). Uniqueness also follows directly from the reflector's injective precomposition map. Taking identities under these Hom bijections identifies the units and counits. Direct image preserves completeness by the direct-image-limits node (and on the constant side by completed-pullback-adjunction); thus the adjunctions are on the full complete subcategories as required. Finally the explicit conjugate formula, using just the identified units and counits, carries the specified direct-image composition and identity maps to their corresponding completed pullback comparisons. This proves all of (1).

Cited nodes: lem-weil-pbc-flat-ringed-diagram-restriction, lem-weil-pbc-constant-completion-equivalence, lem-weil-pbc-ringed-koszul-completion-reflector, lem-sp-completed-pullback-adjunction, prop-weil-pbc-direct-image-limits, def-weil-pbc-adjunction-conjugate.

### Original step 11

Apply $\Psi=\phi$ from Steps 9–10 to $(u,L)=(g',K)$. Its defining formula is precisely
$$\mathcal L(\rho_{g',K})\lambda\,r(r_{g',K})=r_{g',K}^0\phi_{g'}.$$
For the source apply it to $(u,L)=(g,Rf_*K)$; this input is complete by direct-image-limits. Replace $r_YRf_*K$ by $R_f^0\bar K$ through $\chi_f$. Naturality of the completion unit and of its strict quotient diagram gives the comparison $F_g^0\chi_f$ on completed pullbacks and $\mathcal R(G_g\chi_f)$ on the reduction diagram. By Step 4 their composite on the latter diagram is exactly $\rho_M$. With the source reconstruction $r_S$ this yields
$$\mathcal L(\rho_M)\lambda_{\mathcal R^aM}\,r(r_S)=r_S^0(F_g^0\chi_f)\phi_g=r_S^0\iota_S.$$
For clarity the equality of these extensions can be tested by precomposing with the completion unit, where both maps are the strict quotient map followed by $G_g\chi_f$; injectivity of unit precomposition into a complete target, supplied by the reflector, proves the equality. This derives both fixed reconstruction equations in (3).

Cited nodes: def-weil-pbc-completed-pullback, prop-weil-pbc-direct-image-limits, lem-weil-pbc-ringed-koszul-completion-reflector, lem-sp-completion-mate-comparison.

### Original step 12

The source normalization now follows by functoriality. Since $s^a=\mathcal L^a(H^a)r_S$, naturality of $\lambda$ and Step 5 give
$$\begin{aligned}
\mathcal L(\beta)\lambda_{B^a}r(s^a)
&=\mathcal L(\beta\,r(H^a))\lambda_{\mathcal R^aM}r(r_S)\\
&=\mathcal L(H^0)\mathcal L(\rho_M)\lambda_{\mathcal R^aM}r(r_S)\\
&=\mathcal L(H^0)r_S^0\iota_S=s^0\iota_S.
\end{aligned}$$
The last equality uses exactly the definition of $s$ in completion-mate-comparison, so an arbitrary source isomorphism has not been substituted.

Cited nodes: prop-weil-pbc-rlim-functoriality, lem-sp-completion-mate-comparison.

### Original step 13

For the target put $u=f'$ and $Z=\mathscr L_{g'}\mathcal R_X^aK$, and abbreviate $\rho_{g',K}$ to $q$. The definitions give
$$c^a=\kappa_u^a(Z)Ru_*(r_{g',K}),\quad
\delta=(R_u^{\mathcal T}q)d_{u,Z},\quad
t^0=\kappa_u^0(G_{g'}\mathcal R_X\bar K)R_u^0(r_{g',K}^0).$$
Use the comparison square of Step 2, followed by naturality of $\kappa_u^0$ for $q$ and of $\chi_u$ for $r_{g',K}$. It gives, in the written order,
$$\begin{aligned}
\mathcal L(\delta)\lambda_{D^a}r(c^a)
&=\kappa_u^0(G_{g'}\mathcal R_X\bar K)\,
R_u^0\bigl(\mathcal L(q)\lambda_Zr(r_{g',K})\bigr)\chi_{u,F_{g'}^aK}\\
&=\kappa_u^0(G_{g'}\mathcal R_X\bar K)R_u^0(r_{g',K}^0\phi_{g'})\chi_{u,F_{g'}^aK}\\
&=t^0(R_u^0\phi_{g'})\chi_{u,F_{g'}^aK}=t^0\iota_T.
\end{aligned}$$
The second equality is the target reconstruction identity of Step 11. The direct-image-limits statement and completion-mate-comparison specify their $c^a,t^0$ by the K-injective direct-image/limit comparison used in Step 2. Thus this calculation proves compatibility of those specified comparisons, including $\chi,\lambda,\delta$, rather than assuming a finite-reduction normalization.

Cited nodes: prop-weil-pbc-direct-image-limits, lem-sp-completion-mate-comparison, lem-weil-ringed-tower-pushforward-limit-comparison.

### Original step 14

Apply $\mathcal L$ to Step 7 and use naturality of $\lambda$. Substitute the source and target normalizations of Steps 12–13 into $x_K^a=(c^a)^{-1}\mathcal L^a(v^a)s^a$ and cancel the isomorphisms in order:
$$\begin{aligned}
\iota_Tr(x_K^a)
&=(t^0)^{-1}\mathcal L(\delta)\lambda_{D^a}\,r(\mathcal L^a(v^a))r(s^a)\\
&=(t^0)^{-1}\mathcal L(\delta\,r(v^a))\lambda_{B^a}r(s^a)\\
&=(t^0)^{-1}\mathcal L(E^{\mathcal T})\mathcal L(\beta)\lambda_{B^a}r(s^a)\\
&=(t^0)^{-1}\mathcal L(E^{\mathcal T})s^0\iota_S.
\end{aligned}$$
All transformations in the construction are natural: the scalar and finite-reduction comparisons, the adjuncts, completion units, and the K-injective limit comparisons. The displayed derivations are operations on those transformations, hence hold naturally for every morphism of complete $K$. Completed pullback lands in the complete category by its reflector description, and direct image preserves that category; the same proof therefore applies to those intermediate complete inputs. Completion-mate-comparison identifies the right-hand expression with the completed constant-coefficient mate; its Noetherian and perfect-quotient hypotheses are those of the datum. No identity-square or pasting law is used.

Cited nodes: prop-weil-pbc-rlim-functoriality, lem-sp-completion-mate-comparison, lem-sp-completed-pullback-adjunction, prop-weil-pbc-direct-image-limits.

