# Q122 stage-1 report

## Files written

The item keeps its statement and stmt_deps byte for byte. Its proof is now six assembly steps (1679 characters), implementing the released 2026-10-22 repair note, with six new statement-only arguments. All new nodes are unsplit, not Mathlib leaves. They have no proof steps, no proof dependencies and no proof sketch in their statements. The old arguments are retained verbatim below for their future workers.

- dag/nodes/sec-poincare-duality/lem-pod-reindexing-hom-resolution-model.json: statement; no complete Mathlib match. Exact reindexing preserves completed module resolutions and unbounded derived sheaf Hom.
- dag/nodes/sec-poincare-duality/lem-pod-reindexing-evaluation-shift-composition.json: statement; no complete Mathlib match. Evaluation normalization and signed coherence of the reindexed Hom complex.
- dag/nodes/sec-poincare-duality/lem-pod-reindexing-completion-unit-tensor.json: statement; no complete Mathlib match. Projection normalized reindexing of quotient completion and completed tensor.
- dag/nodes/sec-poincare-duality/lem-pod-reindexing-completed-evaluation-reflection.json: statement; no complete Mathlib match. Completion reflector transfers evaluation and coherent internal Hom reindexing.
- dag/nodes/sec-poincare-duality/lem-pod-reindexing-system-hom-reduction-square.json: statement; no complete Mathlib match. Reindexing internal Hom on actual derived coefficient systems and its reduction square.
- dag/nodes/sec-poincare-duality/lem-pod-reindexing-hom-coefficient-descent.json: statement; no complete Mathlib match. Finite free coefficient and localized morphism descent of reindexed evaluation.

The item JSON, citations.json and this report are also written. searches.jsonl and search-results/ preserve the actual search outputs. original-proof.json preserves the original sixteen steps; write_split.py and write_report.py are sandbox-only editing helpers.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag, declaration name and automorphism/Hom terminology found underived adic sheaf comparisons, not this all-stage derived statement. The recorded lean/Sheaf/Paper/DerivedAutomorphismHomEvaluation.lean theorem still has sorry (lines 1836-1872); it is not an attachment.

## WANTED

None: this is redistribution of the already agent-formulated enhancement, not a claim that an unavailable reference supplies it.

## Repair order and source limitations

The live split and passing historical review are explicitly reopened by coord/repair-notes/lem-pod-derived-automorphism-hom-evaluation.json. The human requires at least four comparable independent arguments and an assembly under 3000 characters. Six arguments carry all sixteen original steps. No statement or statement dependency of the item changes; no chapter/unit route changes. New dependencies between helper statements follow the construction order, and none refers back to the item.

I read GOAL.md, the three blueprint levels in SETUP.md, the chapter and sk-def-weil records, and main-20261015 prop-pod-dual-tate-data-compatibility.proof.md Steps 1, 2, 4 and 5. Those steps need automorphism Hom, evaluation and coefficient transport. Stacks 0GMX, sites-modules.tex remark-pullback-internal-hom, only constructs the underived map: it does not prove derived completion, preservation of resolution classes, or coherent coefficient-system identities. Sources on the new nodes explicitly mark those parts agent-formulated. I also read algebraization.tex lemma-derived-completion (099B), lemma-derived-completion-koszul (0A0E), and proetale.tex lemma-naive-completion (099M). These supply completion and its unit, not a ready-made automorphism evaluation theorem. No SGA route is used.

## Review by Q122

I checked delivery-errors B to E against the actual node statements. Each helper introduces its prime, coefficient extension, sites, coefficient sheaves, isomorphism and operations, and states derived isomorphisms rather than only isomorphisms of cohomology groups. Its inline definition/tool references are statement dependencies. The unbounded ambient input category is distinguished from the constructible integral domain and its extra Hom-constructibility condition. New nodes are genuine intermediate comparison arguments, not six copies of the final all-stage theorem. Their statements contain no proof; the full inherited arguments below give the next workers the intended construction.

Assembly step 1 cites the resolution-model statement, whose final paragraph expressly gives c^0 for arbitrary unbounded inputs and identifies finite pullback with the specified functor. Its completed-ring paragraph fixes the actual quotient projections. This covers original steps 1-3: reverse site reindexing, completed module actions, transport of null homotopies and flatness, the infinite-product Hom complex and resolution independence. Exactness and product preservation are from an equivalence, not from an arbitrary geometric pullback.

Assembly step 2 cites the evaluation/shift/composition statement. It explicitly identifies c^0 by the evaluation equation, states the transposition formula and all integer shifts, and fixes the monoidal pullback compositor. I checked the order M tensor Hom: switching from f tensor x uses Koszul symmetry on both sides. The comparison mu points from pulled-back tensor to tensor of pullbacks, so uncurrying uses its inverse. Original steps 4-7 are retained; the signed-complex and evaluation-normalization work is not hidden in an elementary assembly step.

Assembly step 3 cites the completion-unit/tensor statement. It expressly gives F Rlim = Rlim F, the actual unit u_K, every quotient projection, and identification of completed tensor by both Roos coordinates. I checked completeness is required for F K = completed pullback, not for the ambient resolution comparison. The proof uses K-injectives in the tower category; it never assumes evaluated K-injectives are K-injective. This carries original steps 8-9 and their normalization arguments.

Assembly step 4 cites the reflection statement. Its displayed Hom bijections use N complete and extend ordinary evaluation along the actual tensor completion unit. The statement requires M,N and H(M,N) in the constructible category, so the restriction is typed. It does not assume ordinary tensor is complete or M perfect. The statement expressly transfers naturality, both signed shifts and composition by the unit-normalized comparison of step 3. This carries original steps 10-11. The existing Koszul reflector is used for its stated Hom bijection, not for an unstated claim that ordinary and completed tensors coincide.

Assembly step 5 cites the actual system comparison statement. Its first-input fiberwise formula is restricted to cartesian systems. The scalar-extension transition word includes the inverse first-input transition and the second-input transition. Its beta square is stated in D(S), not inferred from equality at every level; functorial L then preserves that square with the actual reduction/limit unit and counit. I checked original steps 12-13 and the exact statements of lem-coef-derived-system-evaluation-calculus and lem-coef-semilinear-derived-sections: they supply precisely the beta map, normalized inputs and transition/evaluation words being reindexed. Neither arbitrary beta invertibility nor equality detection by derived evaluations has slipped in.

Assembly step 6 cites the coefficient-descent statement. This explicitly contains arbitrary localized sums, finite-free completed coefficient extension, evaluation normalization, a field-tower cocycle, and the common-field equality criterion, covering original steps 14-16. The scalar adjunction tool is about actual derived internal Hom and is normalized by evaluation. Finite freeness allows finite biproducts without perfect inputs; no infinite product/tensor interchange is used for that assertion. Ramified extensions are included through the finite-free completed comparison. All original resolution, completion, scalar-adjunction and operation/scalar tools were opened and read, not merely matched by title.

Edge cases checked: zero inputs and the empty scheme give zero comparisons; g=id gives identities; h followed by g has the compositor in the displayed direction. For complexes concentrated in degree zero the evaluation formula is ordinary f(x); negative shifts and characteristic two use the same integer signs on both sides. Arbitrarily unbounded finite inputs are allowed because F preserves products and K-injectivity; no boundedness argument is used. A nonperfect first input is not excluded, so beta is kept as a map, not upgraded to an isomorphism. At L=E the finite-free scalar comparison is the canonical completion unit and the field cocycle is the identity. Torsion localized morphisms need not be injective images of integral arrows: the sum/bilinearity proof applies in the tensor-product Hom groups directly.

Each proof step is non-elementary and has a verbatim statement quote in citations.json. All six assembly steps are below 2000 characters. The previous long arguments have been assigned to statement-only nodes, with explicit obligations and verbatim retained text below. The item statement and original stmt_deps are unchanged; the maintainer's metadata and Lean records are untouched. No Lean written, no compiler, no Lake, no git commands in the shared repository, no agents started.

## Search assessment

Each helper has actual leanfinder (two phrasings), leansearch, loogle and grep queries in searches.jsonl. Search outputs are preserved, and records quote the exact tool/query strings. The initial two Loogle queries using CategoryTheory.DerivedCategory were invalid-name results, recorded as such; corrected CochainComplex.IsKInjective and DerivedCategory.Q searches were also run. No invalid-name result is treated as mathematical evidence of absence. Both semantic queries and grep supplied the substantive checks.

Read Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean lines 309-368: ofEquiv constructs a transported closed structure, but does not identify the project's fixed resolution-model Hom, signed shifts, completed unit or system beta maps. Read Closed/Ideal.lean and Monoidal/Braided/Reflection.lean: the first is Cartesian and the latter assumes a monoidal reflector and a closed ambient category; neither establishes the actual quotient/Koszul completion and normalized evaluation comparisons here. Other hits are underived sheaf pullbacks, ordinary ModuleCat extension/restriction, or general K-injective invariance under a complex isomorphism, not the specified pro-etale completed-ring equivalence and system comparisons. These nodes need nontrivial construction work, hence remain unsplit and are not declared Mathlib leaves.

## Not duplicates

lem-pod-reindexing-hom-resolution-model vs lem-sf-etale-hom-complex-pullback: the existing node concerns pullback comparison of ordinary sheaf hom complexes and source shifts; it does not state preservation of resolution classes and a completed-ring unbounded derived product-Hom isomorphism. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-hom-resolution-model vs def-real-common-stage-weil-linear-dual: the existing node concerns evaluation universal property of the linear dual of a common-stage weil complex; it does not state preservation of resolution classes and a completed-ring unbounded derived product-Hom isomorphism. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-hom-resolution-model vs def-real-common-stage-lisse: the existing node concerns pro-etale local finite freeness at common rational coefficient stages; it does not state preservation of resolution classes and a completed-ring unbounded derived product-Hom isomorphism. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-hom-resolution-model vs def-pur-signed-line-pullback-normalization-data: the existing node concerns normalized signed pullback families and scalar squares; it does not state preservation of resolution classes and a completed-ring unbounded derived product-Hom isomorphism. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-hom-resolution-model vs def-pur-signed-line-scalar-normalization-data: the existing node concerns signed line powers and normalized scalar comparisons; it does not state preservation of resolution classes and a completed-ring unbounded derived product-Hom isomorphism. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-hom-resolution-model vs lem-pur-signed-line-derived-base-change: the existing node concerns signed line comparisons and their unbounded derived tensor action; it does not state preservation of resolution classes and a completed-ring unbounded derived product-Hom isomorphism. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-hom-resolution-model vs def-sp-canonical-scalar-extension-maps: the existing node concerns canonical unit, tensor, dual and tower maps for scalar extension; it does not state preservation of resolution classes and a completed-ring unbounded derived product-Hom isomorphism. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-hom-resolution-model vs lem-pur-ringed-site-pullback-dual-free-chart: the existing node concerns invertibility of a pulled evaluation comparison on a finite-free chart; it does not state preservation of resolution classes and a completed-ring unbounded derived product-Hom isomorphism. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-hom-resolution-model vs lem-pur-ringed-site-pullback-pairing-transfer: the existing node concerns extension of module pairings along a ringed site morphism; it does not state preservation of resolution classes and a completed-ring unbounded derived product-Hom isomorphism. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-hom-resolution-model vs lem-pur-signed-line-scalar-tensor-tower: the existing node concerns dual scalar comparisons of lines and signed tensor and tower coherence; it does not state preservation of resolution classes and a completed-ring unbounded derived product-Hom isomorphism. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-hom-resolution-model vs lem-pur-ringed-site-finite-free-dual-pullback: the existing node concerns pullback of the dual of a finite locally free module on a ringed site; it does not state preservation of resolution classes and a completed-ring unbounded derived product-Hom isomorphism. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-hom-resolution-model vs lem-pur-signed-line-scalar-pullback-square: the existing node concerns pullback of a compatible line scalar square through all signed powers; it does not state preservation of resolution classes and a completed-ring unbounded derived product-Hom isomorphism. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-hom-resolution-model vs lem-pur-inverse-image-hom-comparison: the existing node concerns the unit-normalized internal-hom comparison for an isomorphic base change; it does not state preservation of resolution classes and a completed-ring unbounded derived product-Hom isomorphism. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-hom-resolution-model vs lem-pur-isomorphism-inverse-image-tensor-hom: the existing node concerns inverse image along an isomorphism of schemes commutes with tensor products and sheaf hom; it does not state preservation of resolution classes and a completed-ring unbounded derived product-Hom isomorphism. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-hom-resolution-model vs lem-pod-derived-automorphism-hom-evaluation: the item states the final four-stage comparison; this helper isolates exact reindexing preserves completed module resolutions and unbounded derived sheaf hom, with explicit model-level intermediate conclusions, as required by the human re-split order.

lem-pod-reindexing-evaluation-shift-composition vs lem-sf-etale-hom-complex-pullback: the existing node concerns pullback comparison of ordinary sheaf hom complexes and source shifts; it does not state evaluation-normalized unbounded derived Hom comparison with both signed shifts and the specified scheme-isomorphism compositor. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-evaluation-shift-composition vs def-real-common-stage-weil-linear-dual: the existing node concerns evaluation universal property of the linear dual of a common-stage weil complex; it does not state evaluation-normalized unbounded derived Hom comparison with both signed shifts and the specified scheme-isomorphism compositor. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-evaluation-shift-composition vs def-real-common-stage-lisse: the existing node concerns pro-etale local finite freeness at common rational coefficient stages; it does not state evaluation-normalized unbounded derived Hom comparison with both signed shifts and the specified scheme-isomorphism compositor. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-evaluation-shift-composition vs def-pur-signed-line-pullback-normalization-data: the existing node concerns normalized signed pullback families and scalar squares; it does not state evaluation-normalized unbounded derived Hom comparison with both signed shifts and the specified scheme-isomorphism compositor. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-evaluation-shift-composition vs def-pur-signed-line-scalar-normalization-data: the existing node concerns signed line powers and normalized scalar comparisons; it does not state evaluation-normalized unbounded derived Hom comparison with both signed shifts and the specified scheme-isomorphism compositor. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-evaluation-shift-composition vs lem-pur-signed-line-derived-base-change: the existing node concerns signed line comparisons and their unbounded derived tensor action; it does not state evaluation-normalized unbounded derived Hom comparison with both signed shifts and the specified scheme-isomorphism compositor. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-evaluation-shift-composition vs def-sp-canonical-scalar-extension-maps: the existing node concerns canonical unit, tensor, dual and tower maps for scalar extension; it does not state evaluation-normalized unbounded derived Hom comparison with both signed shifts and the specified scheme-isomorphism compositor. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-evaluation-shift-composition vs lem-pur-ringed-site-pullback-dual-free-chart: the existing node concerns invertibility of a pulled evaluation comparison on a finite-free chart; it does not state evaluation-normalized unbounded derived Hom comparison with both signed shifts and the specified scheme-isomorphism compositor. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-evaluation-shift-composition vs lem-pur-ringed-site-pullback-pairing-transfer: the existing node concerns extension of module pairings along a ringed site morphism; it does not state evaluation-normalized unbounded derived Hom comparison with both signed shifts and the specified scheme-isomorphism compositor. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-evaluation-shift-composition vs lem-pur-signed-line-scalar-tensor-tower: the existing node concerns dual scalar comparisons of lines and signed tensor and tower coherence; it does not state evaluation-normalized unbounded derived Hom comparison with both signed shifts and the specified scheme-isomorphism compositor. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-evaluation-shift-composition vs lem-pur-ringed-site-finite-free-dual-pullback: the existing node concerns pullback of the dual of a finite locally free module on a ringed site; it does not state evaluation-normalized unbounded derived Hom comparison with both signed shifts and the specified scheme-isomorphism compositor. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-evaluation-shift-composition vs lem-pur-signed-line-scalar-pullback-square: the existing node concerns pullback of a compatible line scalar square through all signed powers; it does not state evaluation-normalized unbounded derived Hom comparison with both signed shifts and the specified scheme-isomorphism compositor. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-evaluation-shift-composition vs lem-pur-inverse-image-hom-comparison: the existing node concerns the unit-normalized internal-hom comparison for an isomorphic base change; it does not state evaluation-normalized unbounded derived Hom comparison with both signed shifts and the specified scheme-isomorphism compositor. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-evaluation-shift-composition vs lem-pur-isomorphism-inverse-image-tensor-hom: the existing node concerns inverse image along an isomorphism of schemes commutes with tensor products and sheaf hom; it does not state evaluation-normalized unbounded derived Hom comparison with both signed shifts and the specified scheme-isomorphism compositor. Its underived or more restricted content is reused through the recorded operations/tools, not duplicated as a separate new assertion.

lem-pod-reindexing-evaluation-shift-composition vs lem-pod-derived-automorphism-hom-evaluation: the item states the final four-stage comparison; this helper isolates evaluation normalization and signed coherence of the reindexed hom complex, with explicit model-level intermediate conclusions, as required by the human re-split order.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sbc-koszul-fibre-linear-descent: the existing node concerns linear descent of the explicit koszul product-fibre construction; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs prop-weil-pbc-levelwise-truncations: the existing node concerns levelwise truncations of the adic tower; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sbc-koszul-tensor-derived-tower: the existing node concerns ordinary koszul tensor towers represent derived tensor towers; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-fix-bounded-projective-tensor-complete: the existing node concerns canonical completeness of bounded projective sheaf tensors; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sf-completed-tensor-rational-naturality: the existing node concerns naturality and rationalization of a completed tensor comparison; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sf-open-roos-unit-adjunction: the existing node concerns roos completeness, actual open completion units and the complete adjunction; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sf-regular-roos-koszul-unit: the existing node concerns regular quotient roos completeness detects the canonical koszul unit; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-sf-integral-koszul-intrinsic-unit: the existing node concerns integral one-uniformizer intrinsic koszul unit; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-sf-koszul-small-model-completed-tensor: the existing node concerns local derived completeness and completed tensor on the canonical small site model; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sf-automorphism-completion-unit-comparison: the existing node concerns automorphism pullback commutes with completion with a unique unit normalization; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sf-constructible-canonical-completeness: the existing node concerns from an intrinsic presentation witness to canonical actual completeness; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sf-open-quotient-koszul-completeness: the existing node concerns dvr quotient augmentation, koszul completion and open completeness; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sf-derived-completed-tensor-bilinearity: the existing node concerns bilinearity of derived completed tensor and its rational hom action; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-fix-qcqs-completion-unit-locality: the existing node concerns canonical completion units and finite open–closed locality on qcqs schemes; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs det-prop-diagonal-tower-system: the existing node concerns the torsion diagonal classes as one morphism of inverse systems; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sfb-integral-pullback-strict-roos-normalization: the existing node concerns strict roos normalization of integral pullback and constant scalar restriction; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sfb-ringed-complete-triangulated: the existing node concerns exact koszul completion and the triangulated complete locus; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sfb-exact-completed-koszul-pullback: the existing node concerns exact product-preserving inverse image transports the actual koszul unit; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sfb-adic-stratum-completion-unit: the existing node concerns restriction of the completion unit to strata and covering slices; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sfb-adic-complete-reduction-cone: the existing node concerns normalized quotient homotopy-limit cone for a complete object; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sfb-integral-roos-derived-pullback-unit: the existing node concerns derived interpretation of the integral pulled quotient roos augmentation; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sfb-qcqs-closed-pullback-finite-model-completion: the existing node concerns constructible closed inverse image preserves finite scalar models, tor bounds and adic completion; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sfb-adic-complete-residue-conservative: the existing node concerns residue reduction is conservative on locally complete objects; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-a1-principal-completed-koszul-towers: the existing node concerns actual completed-coefficient principal koszul and quotient tensor towers; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-a1-roos-intrinsic-unit-comparison: the existing node concerns the canonical roos, strict-limit and intrinsic koszul units agree; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-a1-principal-intrinsic-completion: the existing node concerns principal intrinsic fiber and its specified chain unit; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-a1-principal-augmented-roos-descent: the existing node concerns the specified augmented principal tower comparison descends; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-completed-koszul-quotient-roos-augmentation: the existing node concerns the completed strict koszul quotient augmentation on roos models; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-weil-pbc-completed-quotient-ordinary-unit: the existing node concerns ordinary completed quotient-limit unit; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-derived-exact-equivalence-squares: the existing node concerns compatible derived squares under exact equivalences; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-ringed-cech-completion-unit-idempotence: the existing node concerns idempotence of the two actual cech completion unit maps; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-weil-pbc-flat-scalar-koszul-models: the existing node concerns ordered coordinate and restriction models for scalar koszul towers; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-completed-koszul-product-comparison: the existing node concerns finite koszul comparison induces the normalized product-fiber comparison; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-ringed-cech-completion-restriction: the existing node concerns unit-normalized restriction of cech completion; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-weil-pbc-completed-quotient-completion-unit: the existing node concerns bundled specified completed quotient-completion unit; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-completed-fiber-strict-limit-comparison: the existing node concerns published completed koszul fiber computes the strict derived limit; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-completed-scalar-unit-adjunction: the existing node concerns completion-unit normalization of scalar adjunction and pullback reconstruction; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-levelwise-isomorphism-cones: the existing node concerns levelwise isomorphisms and complete cones; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-koszul-localization-assembly: the existing node concerns localization assembly for the koszul comparison; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-strict-quotient-pullback-compatibility: the existing node concerns pullback coherence of normalized strict scalar balancing; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-reconstruction-uniform-tower: the existing node concerns reconstruction of a uniform local tower; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-completed-fiber-roos-representative-comparison: the existing node concerns the explicit koszul comparison is compatible with every derived representative; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-constant-completion-unit-normalization: the existing node concerns constant quotient completion unit on every complex; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-completed-fiber-cech-comparison: the existing node concerns published completed koszul fiber compared with cech internal hom; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-quotient-diagram-scalar-projection: the existing node concerns strict quotient balancing preserves the diagram projection formula; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-strict-quotient-scalar-balancing: the existing node concerns strict quotient balancing and pullback preserve the quotient augmentation; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs prop-weil-pbc-koszul-reconstruction-comparison: the existing node concerns comparison of completed koszul and quotient derived limits; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-finite-free-completion-transport: the existing node concerns finite-free scalar extension commutes with completion and its unit; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-ordered-exchange-coefficient-comparison: the existing node concerns coefficient normalization of the raw ordered completed exchange; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-constant-completion-equivalence: the existing node concerns constant-to-completed coefficients on derived-complete categories; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-weil-pbc-adic-coefficient-datum: the existing node concerns tower category and adic coefficient datum; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-completed-pullback-reflection: the existing node concerns reflection through the specified completed pullback unit; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-completed-fiber-roos-comparison: the existing node concerns finite exterior koszul and ordered tensor-dual towers agree; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-strict-scalar-completion-unit: the existing node concerns strict quotient completion units commute with normalized scalar restriction; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-completed-constant-presentation-transport: the existing node concerns joint transport of the completed quotient and koszul presentations; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-flat-constant-tensor-pro-zero-cones: the existing node concerns flat constant extension and k-flat tensor of pro-zero cone towers; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-flat-scalar-koszul-tower-comparison: the existing node concerns restriction of scalars identifies strict koszul towers and their units; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-completed-constant-coefficient-equivalence: the existing node concerns scalar and strict quotient compatibility of the completed coefficient equivalence; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-completed-koszul-quotient-comparison: the existing node concerns unit-compatible koszul-to-quotient comparison in the completed coefficient presentation; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs prop-weil-pbc-koszul-reconstruction: the existing node concerns koszul and quotient reconstruction; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-derived-cochain-counit: the existing node concerns derived counit on complex localization; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-completed-koszul-constant-transport: the existing node concerns koszul completion under a scalar-preserving completed coefficient isomorphism; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-ringed-localization-rhom-calculus: the existing node concerns derived internal hom and localization of a bounded localization complex; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-extended-cech-reflector-core: the existing node concerns extended cech completion core reflector clauses; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-weil-pbc-strict-quotient-scalar-balancing-data: the existing node concerns normalized strict scalar-balancing data; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-ringed-koszul-completion-reflector: the existing node concerns ringed koszul reflector; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-completed-quotient-unit-normalization: the existing node concerns actual completed quotient unit on a k-flat complex; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-finite-reduction-reconstruction: the existing node concerns finite reduction of reconstruction; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-derived-cochain-right-unit: the existing node concerns derived unit on complex localization; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-ringed-cech-completion-hom-injective: the existing node concerns unit cancellation for morphisms between cech completed objects; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-derived-exact-equivalence-square-data: the existing node concerns data of compatible exact-equivalence derived squares; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-weil-pbc-intrinsic-completion: the existing node concerns intrinsic derived completion; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-derived-cochain-comparison-factors: the existing node concerns localization comparison for an additive functor on complexes; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-completed-koszul-reduction-roos-triangle: the existing node concerns normalized quotient roos triangle on explicit koszul completion; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-finite-free-strict-tower-transport: the existing node concerns canonical finite-free tensor comparison for derived products and strict towers; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-pbc-strict-scalar-koszul-comparison: the existing node concerns strict scalar comparison for finite ordered koszul towers; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-weil-pbc-completed-constant-presentation-data: the existing node concerns common constant presentation of the two completion objects; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-pur-strict-quotient-diagonal-normalization: the existing node concerns strict quotient reduction model and completion-unit normalization; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-pur-integral-principal-cone-quotient-comparison: the existing node concerns unit-preserving scalar-cone comparison with actual finite integral quotients; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-pur-strict-quotient-completion-data: the existing node concerns strict quotient reduction towers and their canonical completion data; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-pur-principal-koszul-quotient-towers: the existing node concerns canonical principal koszul and quotient towers with tensor augmentations; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-pur-integral-principal-cone-local-criterion: the existing node concerns local vanishing criterion for the independent-universe principal cone completion; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-pur-adic-site-strict-quotient-interface: the existing node concerns small-site adic strict quotient interface and canonical normalizations; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sf-completion-finite-reduction: the existing node concerns finite reduction inverts the completion unit; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-pur-integral-principal-cone-quotient-augmentation: the existing node concerns normalized levelwise principal-cone augmentation to actual integral quotients; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-cbc-signed-koszul-model-exists: the existing node concerns normalized negative koszul completion model exists and preserves quasi-isomorphisms; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-pur-completed-coefficient-completion-roos-transport: the existing node concerns the normalized completion roos triangle under completed coefficient transport; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-pur-integral-operation-roos-effectivity: the existing node concerns effectivity of the strict finite-operation roos towers; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-weil-completed-integral-principal-unit-criterion: the existing node concerns the normalized principal quotient unit detects actual integral derived completeness; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-cbc-exact-linear-koszul-fiber: the existing node concerns exact linear functors preserve the signed koszul completion model; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-pur-principal-koszul-roos-presentation-comparison: the existing node concerns normalized comparison of principal koszul roos completion with dual koszul presentations; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sp-completion-mate-comparison: the existing node concerns the strict quotient-tower exchange realizes the completed-adjunction mate; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-pur-completed-reduction-augmentation-iso: the existing node concerns the specified strict quotient augmentation of a complete object is invertible; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-pur-principal-cone-tower: the existing node concerns augmented positive-power cone tower of a chain endomorphism; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sf-quotient-tower-evaluation-complex: the existing node concerns explicit finite evaluation of a quotient-tower complex; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-pur-unit-power-completeness: the existing node concerns local derived completeness is unchanged by a unit times a positive power; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-pur-roos-intrinsic-completeness-equivalence: the existing node concerns roos and intrinsic completeness for completed local-field coefficients; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-pur-regular-quotient-completion-unit: the existing node concerns canonical regular quotient completion unit criterion; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-pur-derived-complete-koszul-reconstruction: the existing node concerns koszul reconstruction of a derived-complete reduction tower; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sf-cbc-compact-support-composition-limit: the existing node concerns normalized reconstruction of composites of completed operations; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-pur-principal-koszul-roos-reflector: the existing node concerns reflection property of the principal koszul roos complex; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs def-cbc-signed-koszul-completion-model: the existing node concerns the pure-tensor-normalized signed koszul completion model; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sf-completion-unit-finite-projection: the existing node concerns projection of the completion unit is the finite scalar-extension unit; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sp-completed-pullback-adjunction: the existing node concerns completed pullback is left adjoint to direct image; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-cbc-signed-koszul-finite-coordinates: the existing node concerns finite pure-tensor coordinates of the ordered negative koszul tensors; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-sf-cbc-extension-zero-completion: the existing node concerns strict reduction of completed extension by zero; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completed-evaluation-reflection vs lem-fix-scalar-completion-associator: the existing node concerns tensor-associator normalization of the strict-tower scalar completion comparison; this helper concerns the completed tensor-Hom evaluation/transposition bijection and transfer of the ambient automorphism Hom comparison with signed shifts and composition, on the constructible-Hom domain. It uses the general reflector/quotient-unit facts but must additionally identify the actual evaluation and reindexing maps.

lem-pod-reindexing-completion-unit-tensor vs lem-pur-isomorphism-completed-reduction-reindexing: that existing node supplies reduction/limit reindexing and completed direct-image mates; the new argument adds the fixed completed tensor comparison with both Roos coordinates and substitution coherence. The common reduction/limit facts are existing source tools, not a replacement theorem.

lem-pod-reindexing-completion-unit-tensor vs lem-sf-automorphism-completion-unit-comparison: that node is an abstract completion-unit square for an automorphism of one scheme, without the canonical quotient-tower tensor normalization, substitutions and both cone coordinates asserted here.

lem-pod-reindexing-system-hom-reduction-square vs lem-coef-derived-system-evaluation-calculus: the existing node constructs R, L, I and beta; it does not identify their naturality under the ringed site equivalence as the same simultaneous Hom-complex reindexing map. The new node states that identification and its beta square.

lem-pod-reindexing-system-hom-reduction-square vs lem-coef-semilinear-derived-sections: the existing node supplies the cartesian first-input formula and transition word; the new node identifies the isomorphism-of-sites Hom comparison and integral beta square using those constructions.

lem-pod-reindexing-hom-coefficient-descent vs lem-pur-integral-operations-scalar-extension: the existing node gives operation/scalar isomorphisms and cocycles; the new argument identifies the evaluation-defined c^0, its inverse and arbitrary localized arrow identities through those comparisons.

lem-pod-reindexing-hom-coefficient-descent vs lem-sfb-dc-hom-scalar-adjunction: the existing node gives a restriction-of-scalars Hom adjunction, not finite-free Hom base change, its commuting reindexing square or descent to arbitrary localized and common-stage arrows.

## Retained original arguments for the six workers

These are the original texts without omission or compression. They are retained here as source material for each statement-only node, not proof fields of those nodes. The groupings have 2292, 2388, 1573, 1583, 1828 and 2412 characters respectively (approximately, excluding references); all are comparable independent tasks. Their source references and used nodes remain the old proof's references and are listed after each original step.

### lem-pod-reindexing-hom-resolution-model

Original step 1:

Put $F=g^{-1}$, using the covering-preserving equivalence $(U\to X)\mapsto(U\to X\xrightarrow gY)$. Its quasi-inverse is inverse image along $g^{-1}$. Thus $F$ is exact, preserves products and coproducts, and identifies constant finite coefficient sheaves, compatibly with every quotient map. Also
$F\widehat{\mathcal O}_{E,Y}=F\lim_n(A_{E,n})_Y\cong\lim_n(A_{E,n})_X=\widehat{\mathcal O}_{E,X}$.
This is the actual comparison induced by all the projections. Reindexing sheaves and their module actions gives mutually inverse module equivalences for these completed ring sheaves as well: the inverse coefficient map is obtained by the same construction for $g^{-1}$ and their composites are identities on every projection. The tensor and sheaf-Hom comparisons are those on local sections, $s\otimes t\mapsto Fs\otimes Ft$ and $f\mapsto Ff$.

Uses: lem-weil-proetale-isomorphism-inverse-image, lem-pur-isomorphism-inverse-image-tensor-hom

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 0GMX (remark-pullback-internal-hom), enhanced by the stated resolution constructions"}

Original step 2:

These equivalences preserve the resolution classes directly. If $I$ is K-injective and $A$ is acyclic, a chain map $A\to FI$ corresponds under the inverse exact equivalence to a map $F^{-1}A\to I$; its null homotopy transports back. If $Q$ is K-flat, then $A\otimes FQ\cong F(F^{-1}A\otimes Q)$ is acyclic. Flat terms are preserved by the same argument on short exact sequences. Exactness carries quasi-isomorphisms to quasi-isomorphisms, and termwise application descends to the derived categories with the specified shift comparison. The termwise unit and counit still give inverse derived equivalences. At finite coefficients this derived functor is exactly $P=Lg^*$ in the question.

Uses: def-pur-kinjective-complex, def-pc-kflat-complex, lem-pur-isomorphism-inverse-image-tensor-hom, lem-weil-pbc-exact-functor-derived-factorization

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 0GMX (remark-pullback-internal-hom), enhanced by the stated resolution constructions"}

Original step 3:

For finite coefficients, and separately in the ambient completed-ring module category, choose a representative $K$ of $M$ and a K-injective representative $I$ of $N$. In Hom degree $r$ the sheaf comparisons of Step 1 give
$F\prod_p\mathcal Hom(K^p,I^{p+r})\cong\prod_p\mathcal Hom(FK^p,FI^{p+r})$.
They commute with $d(f)=d_I f-(-1)^r f d_K$, so define an isomorphism of Hom complexes. Step 2 makes $FI$ an admissible K-injective representative. Consequently localization gives an isomorphism $c:FH(M,N)\cong H(FM,FN)$. Naturality holds on maps of complexes, and independence of representatives and descent in both variables follow from the cited quasi-isomorphism invariance of Hom complexes. In particular this covers arbitrary unbounded finite-coefficient inputs.

Uses: def-pur-derived-internal-hom, def-pur-hom-complex, lem-pur-rhom-well-defined

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 0GMX (remark-pullback-internal-hom), enhanced by the stated resolution constructions"}

### lem-pod-reindexing-evaluation-shift-composition

Original step 4:

The cited internal currying isomorphism, followed by global-Hom recovery, gives the tensor-Hom transposition bijection. Use flat-term K-flat representatives for the tensor inputs. The canonical tensor comparison $\mu$ is induced by the ordinary comparison on their total tensor complexes. Evaluation is ordinary Hom-complex evaluation followed by the inverse localized augmentation of the target. Reindexing the pure-tensor evaluation $f\otimes x\mapsto f(x)$ gives the same chain map on either side. When evaluation is written in the order $x\otimes f$, both sides use the same Koszul symmetry. Thus
$\operatorname{ev}_{FM,FN}(1\otimes c)\mu=F(\operatorname{ev}_{M,N})$.
The closed adjunction and its representative normalization identify this $c$ with the evaluation-defined comparison; the transposition bijection makes it the unique map satisfying this equation.

Uses: lem-pc-kflat-resolution, lem-weil-pbc-ringed-internal-hom-exact-restriction, lem-pur-rhom-global-sections, lem-sfb-ringed-derived-monoidal-comparisons, def-coef-ringed-tensor-hom-model

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 0GMX (remark-pullback-internal-hom), enhanced by the stated resolution constructions"}

Original step 5:

For $b:M\otimes^L L\to N$ write $b=\operatorname{ev}_{M,N}(1\otimes b^\sharp)$. Apply $F$ and the naturality of $\mu$. Step 4 gives
$F(b)\mu_{M,L}^{-1}=\operatorname{ev}_{FM,FN}(1\otimes(cF(b^\sharp)))$.
Applying the inverse of the transposition bijection proves the displayed transposition formula. It also proves naturality in $M,N$: after uncurrying either side of the naturality square one obtains the same composite of evaluation with the two input maps.

Uses: def-coef-ringed-tensor-hom-model

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 0GMX (remark-pullback-internal-hom), enhanced by the stated resolution constructions"}

Original step 6:

The shift comparison for $F$ is identity in each degree. The Hom-complex identifications for $H(M[a],N[b])$ reindex the factors and multiply by the usual signs coming from $d_{K[a]}=(-1)^a d_K$. Step 3 applies $F$ to the same factors and the same integer signs, so its square with each of these identifications commutes as a square of complexes. It therefore commutes in the derived category. This checks shifts in both Hom inputs, rather than only a shift of the output.

Uses: lem-weil-pbc-exact-functor-derived-factorization, def-pur-hom-complex

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 0GMX (remark-pullback-internal-hom), enhanced by the stated resolution constructions"}

Original step 7:

For a second scheme isomorphism $h:Z\to X$, identify $P_{gh}$ with $P_hP_g$ by the canonical derived pullback-composition map. The two candidate internal-Hom comparisons become equal after uncurrying: both give $P_hP_g(\operatorname{ev})$, since the tensor-composition square in the cited statement commutes. Injectivity of transposition proves the composition identity for $c$. For the identity scheme map it similarly gives the identity comparison. This is also visible before localization: two successive reindexings send a local homomorphism $f$ to $h^{-1}g^{-1}f$ in either construction.

Uses: lem-sfb-ringed-derived-monoidal-comparisons, def-coef-ringed-tensor-hom-model

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 0GMX (remark-pullback-internal-hom), enhanced by the stated resolution constructions"}

### lem-pod-reindexing-completion-unit-tensor

Original step 8:

Now work integrally. For a derived-complete input $K$, the canonical quotient-tower unit $u_K:K\to\mathcal L_Y\mathcal R_YK$ is an isomorphism: apply the finite-free completed-scalar comparison with $L=E$. In particular this is the canonical unit, not an arbitrarily chosen isomorphism with a Roos triangle. Reindexing takes each reduction to the corresponding reduction of $FK$ and commutes with its quotient maps. It commutes with total derived inverse limit: apply it termwise to a K-injective resolution in the abelian tower category; Step 2's null-homotopy argument applies to tower maps, and the ordinary limit commutes with this equivalence. Hence
$F\mathcal L_Y\mathcal R_YK\cong\mathcal L_X F_\bullet\mathcal R_YK=Lg^*K$.
Composing with $F(u_K)$ gives the claimed natural identification $FK\cong Lg^*K$, with all its reduction projections fixed.

Uses: lem-weil-finite-free-completed-scalar-comparison, lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-coef-derived-system-evaluation-calculus, def-weil-derived-pullback-tensor-hom

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 0GMX (remark-pullback-internal-hom), enhanced by the stated resolution constructions"}

Original step 9:

The same calculation applied to the actual strict tensor-reduction complexes identifies $F(M\widehat\otimes^L N)$ with $FM\widehat\otimes^L FN$. On a flat-term K-flat model it reindexes each total-tensor summand, and on the Roos realization it reindexes both product coordinates and $1-s$. This is the specified completed tensor comparison, since that comparison is fixed by precisely these representative and Roos-coordinate equations. Coefficient transitions commute before taking the limit. The comparison is invertible, with inverse given by inverse reindexing. Substitution of normalized tensor/pullback systems shows that composition, symmetry, and shift comparisons have the same normalization after realization.

Uses: def-pur-completed-pullback-tensor-comparison, lem-pur-completed-operation-tower-substitution

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 0GMX (remark-pullback-internal-hom), enhanced by the stated resolution constructions"}

### lem-pod-reindexing-completed-evaluation-reflection

Original step 10:

To check integral evaluation against completed tensor, use the completion reflector. The constant-completion comparison identifies quotient-tower completion with Koszul completion, respecting its unit. The reflector then gives, for a complete target $N$,
$\operatorname{Hom}(\widehat{M\otimes^LL},N)\cong\operatorname{Hom}(M\otimes^LL,N)\cong\operatorname{Hom}(L,H(M,N))$.
Here the hat is the functorial completion of the ordinary tensor; its quotient tower is exactly the defining tower of completed tensor. Thus evaluation for completed tensor is the unique extension of ordinary evaluation along the completion unit. This establishes transposition on the complete full subcategory without assuming that ordinary tensor is already complete or that $M$ is perfect.

Uses: lem-weil-pbc-constant-completion-equivalence, lem-weil-pbc-ringed-koszul-completion-reflector, def-coef-ringed-tensor-hom-model

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 0GMX (remark-pullback-internal-hom), enhanced by the stated resolution constructions"}

Original step 11:

Use the ambient completed-ring Hom comparison of Step 3. Under Step 8 it is the required integral $c$. Its source is constructible by the hypothesis on $H(M,N)$ and preservation of the integral category by pullback; hence its target is constructible as well. Precompose its completed evaluation equation with the ordinary-to-completed tensor unit. By Steps 4 and 9 this becomes the already proved ordinary evaluation equation. The reflector's bijection in Step 10 proves equality of the completed maps. Step 5 now proves the integral transposition formula; Steps 6 and 7 prove the shift and composition identities, since completion units and both Roos coordinates commute with reindexing. The hypothesis on the internal Hom is used here to stay on the stated constructible domain, not to obtain its ambient comparison.

Uses: lem-pur-integral-operations-preserve-constructible, lem-weil-pbc-ringed-koszul-completion-reflector

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 0GMX (remark-pullback-internal-hom), enhanced by the stated resolution constructions"}

### lem-pod-reindexing-system-hom-reduction-square

Original step 12:

For the system assertion, reindex the underlying site while keeping the inverse-sequence index and all coefficient quotient arrows. This defines an exact equivalence of the two abelian categories of strict module systems, with an explicit inverse. Step 2 therefore applies to their unbounded derived categories. On their ringed sequence topoi, the product-Hom-complex construction of Step 3 gives an actual internal-Hom comparison and Step 4 gives an actual equality of evaluation maps. For cartesian first inputs its evaluations are the finite-level comparisons, by the fiberwise-Hom identification in the cited semilinear-system statement. In the transition formula of that statement, reindexing commutes with scalar extension, $t^M$, its inverse, $t^N$, and evaluation; consequently it gives the same transpose. Thus the maps respect the specified system transitions, before evaluation at any level.

Uses: lem-coef-semilinear-derived-sections, lem-coef-derived-system-evaluation-calculus

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 0GMX (remark-pullback-internal-hom), enhanced by the stated resolution constructions"}

Original step 13:

The comparison with integral reduction is the square having top $\mathcal R_X(FH(M,N))\to\mathcal R_XH(FM,FN)$ and bottom $F_\bullet\mathcal I_Y(\mathcal R_YM,\mathcal R_YN)\to\mathcal I_X(\mathcal R_XFM,\mathcal R_XFN)$, with vertical maps the specified $\beta$ and the canonical reduction/reindexing identifications. This square commutes as a system square: $\beta$ is defined by the same evaluation, and Step 12's reindexing carries that evaluation chain map and its transpose to themselves. Its unit/counit comparisons are the reduction/limit adjunction's actual unit and counit, so applying the functorial $\mathcal L$ preserves this square and all the evaluation and transposition identities. This proves the demanded realization normalization. It uses neither equality detection by finite evaluations nor invertibility of $\beta$ for arbitrary inputs; the integral Hom comparison is the ambient one already constructed.

Uses: lem-coef-derived-system-evaluation-calculus, lem-coef-semilinear-derived-sections

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 0GMX (remark-pullback-internal-hom), enhanced by the stated resolution constructions"}

### lem-pod-reindexing-hom-coefficient-descent

Original step 14:

Rationalize the integral maps and their inverses. For arbitrary arrows $a=\sum_i a_i\otimes\lambda_i$ and $b=\sum_j b_j\otimes\nu_j$ in localized Hom groups, each naturality or evaluation equation expands by bilinearity to the integral equation for $(a_i,b_j)$ multiplied by $\lambda_i\nu_j$; similarly the transpose identity is linear in its input. The inverse identities and shift/composition identities localize as well. This proves the assertion for arbitrary rational morphisms, rather than just arrows which are integral. These are exactly the localized operations specified in the question.

Uses: def-weil-rationalization-karoubi, def-weil-derived-pullback-tensor-hom

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 0GMX (remark-pullback-internal-hom), enhanced by the stated resolution constructions"}

Original step 15:

For a finite coefficient extension $E\subset L$, its completed coefficient sheaf is finite free over the original completed coefficient sheaf, and ordinary scalar extension agrees canonically with the specified completed one. The evaluation-normalized derived scalar adjunction identifies the restriction of $H_S(S\otimes_R^LM,S\otimes_R^LN)$ with $H_R(M,N\otimes_R^LS)$. On choosing a finite free basis for $S$, the latter is a finite direct sum of copies of $H_R(M,N)$: internal Hom preserves finite biproducts, either by its Hom-complex formula or by the transposition bijection. Therefore the scalar comparison is the direct sum of copies of Step 3's comparison, with evaluation $(f\otimes s)(x\otimes t)=f(x)\otimes st$. Reindexing fixes the coefficient scalars and hence commutes with this map. This argument uses finite direct sums only, so imposes no perfectness condition on the inputs. The formula is basis independent because it is the transpose of evaluation. It commutes with a further extension by associativity of scalar multiplication and tensor reassociation. The existing operation/scalar comparisons therefore carry $c$ to the comparison at the larger field, with its evaluation and shifts.

Uses: lem-weil-finite-free-completed-scalar-comparison, lem-pur-integral-operations-scalar-extension, lem-sfb-dc-hom-scalar-adjunction

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 0GMX (remark-pullback-internal-hom), enhanced by the stated resolution constructions"}

Original step 16:

Represent all objects, arrows and the comparisons over one common finite coefficient field in $\overline{\mathbf Q}_\ell$. Step 15 makes the class of $c$ independent of enlarging that field. If two arrow representatives become equal at a further field, their naturality equations and images under $c$ agree there, hence define equal classes. Evaluation, transposition, inverses, composition and shifts can each be checked at that common field using Steps 11 and 14; their classes have the required identities. This is precisely the common-stage operation construction, and completes all coefficient stages.

Uses: def-weil-algebraically-closed-coefficients, def-weil-derived-pullback-tensor-hom

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 0GMX (remark-pullback-internal-hom), enhanced by the stated resolution constructions"}

## Unfinished work and validation

The six new nodes intentionally remain statement-only for stage-1 workers. No mathematical content is claimed proved in Lean. First server dry run rejected only a mistaken dependency: the mathematical shift [b-a] had been parsed as a node reference. I removed the spurious dependency and spaced the mathematical brackets. I also repaired a Python string escape in the assembly beta notation. The corrected dry run is required before pushing.

Server dry run completed with exit 0: OK (not pushed) deliver/Q122/lem-pod-derived-automorphism-hom-evaluation at 42577c2227f: preflight passed. The only subsequent report edit records this successful validation and the corrected character count.
