# Stage-1 report: lem-sf-bifunctor-homotopy-exact

## Files written

- dag/nodes/sec-six-functors/lem-sf-bifunctor-homotopy-exact.json: split item, unchanged statement, five explicit proof steps.
- dag/nodes/sec-six-functors/lem-sf-signed-bifunctor-cone-iso.json: one new statement-only lemma, unsplit, no Mathlib match.
- citations.json: a verbatim statement quotation for every citation in every item proof step.
- report.md: this report. searches.jsonl contains the actual msearch.py results. write_split.py and write_report.py are sandbox-only preparation scripts.

## Attachments

None. I searched WeilConjectures for the exact blueprint tag, bifunctorHomHomotopyFunctor, and bifunctor Hom/homotopy/cone/shift declarations. CochainComplex.bifunctorHomHomotopyFunctor in CategoryTheory/DerivedCategory/BifunctorHom.lean:60 constructs the underlying functor only; it states no shift or exactness assertion. CochainComplex.bifunctorHomMapLeftHomotopy in Algebra/Homology/BifunctorHomComplex.lean:298 proves homotopy invariance only. Neither covers the whole item, and the derived functors later in BifunctorHom.lean introduce K-injective resolutions unnecessary here.

## WANTED

None. The source and its omitted-details warning are available locally.

## Corrections and limitations

No statement dispute or statement change. The original source is Stacks Tag 08JC, lemma-RHom-triangulated, sites-cohomology.tex:8948. Its proof explicitly omits details and concerns sheaf internal Hom. I retain its termwise-split cone route but mark the general bifunctor proof as agent-written. The blueprint supplies motivation, not a proof of the signed construction.

I read the unit sk-prop-sf-biduality-general and the six-functors chapter record. This is generic exactness infrastructure below Verdier duality, not a new geometric route. I read the inherited blueprint anchors lem-a1-local-boundary-duality.proof.md (use of exact duality) and thm-coef-qbar-verdier.proof.md (exactness at a common finite stage). blueprint_refs ancestor prints null because the maintainer-created parent has created.item null; I retain that approved inherited null anchor and specify its exact intended place. No unit realization is owned by this auxiliary item.

The unnormalized reindexing sign is insufficient for coherent integer shifts. The proof uses s_(K,r) with multiplier (-1)^(rp+r(r+1)/2). The quadratic term supplies the addition law, and its linear normalization fixes the opposite-triangle connecting sign for the negative cone projection used by this project. This specifies a choice allowed by the original existence statement.

The existing lem-weil-pbc-bilinear-hom-complex is not used as a black box: it has the standard differential d_I f-(-1)^n f d_K and asks for all small products, whereas this item has the signed (-1)^p differential and only countable products. The short direct d-squared and functoriality checks avoid introducing either stronger hypotheses or an unjustified convention identification. Existing sheaf Hom shifts and the covariant cone comparison are also not applied outside their stated scope.

## Review by Q68

For the item I read Stacks 08JC in sites-cohomology.tex and the displayed signed differential, product construction, functoriality, cochain and homotopy formulas in WeilConjectures/Algebra/Homology/BifunctorHomComplex.lean:55-304. I read the existing quotient functor in WeilConjectures/CategoryTheory/DerivedCategory/BifunctorHom.lean:39-78. The proof is about the homotopy category, so it does not infer that an arbitrary additive H inverts quasi-isomorphisms.

For the new cone lemma I read the same omitted-details source 08JC, the signed source module, and the cone and shift conventions in Stacks derived.tex (definition-cone, definition-distinguished-triangle, proposition-homotopy-category-triangulated) and homology.tex Tag 011G, definition-shift-cochain. Its statement gives a chain isomorphism, not just cohomology identifications. I checked it directly: additivity in the first variable identifies H(L^p direct-sum K^(p+1),I^q) with the binary biproduct of the two H terms. This uses the biproduct relations H(1)=H(i_L p_L+i_K p_K), and does not need exactness of H. A countable product of these binary biproducts identifies with the binary biproduct of the two countable products by product projections; no products are assumed exact. The two restriction components of d_U are d_X x and (-1)^p(d_I a_p+a_(p+1)d_K-x_(p+1)f). Multiplying a_(j-1) by (-1)^(j-1) gives the second block -d_Y y-tx. Thus the stated theta intertwines the two differentials, and the explicitly stated inverse cancels each sign. Naturality follows on the two summands from the given commuting square. These calculations justify a smaller chain-level lemma; it does not state triangulatedness, shift coherence, homotopy descent, or localization, and is not a restatement of the item.

I opened every cited node and checked what its statement actually supplies. Step 1 cites def-sp-abelian for the additive abelian setting and def-weil-abstract-derived-category for complexes and d-squared zero; its bifunctor/product calculation is written explicitly, not attributed to those definitions as a hidden theorem. Step 2 cites lem-pur-homotopy-category-triangulated for the homotopy category; the homotopy preservation formula is proved in the step. In particular the (-1)^p factor makes the d_I terms cancel and gives coefficient +1 to the two components of f-g. The quotient factorization is just the universal property of chain maps modulo that relation.

Step 3 uses only the shifts actually stated in def-weil-abstract-derived-category. I checked both differential terms and the integer identity b(r+s)=b(r)+b(s)+rs, including negative integers. Opposite shift by m is explicitly underlying shift by -m. I read Mathlib CategoryTheory/Triangulated/Opposite/Basic.lean and Opposite/Triangle.lean: the opposite distinguished triangle reverses the vertices without adding a sign and uses the inverse shifted third arrow. This matches the w[-1] written in step 4.

Step 4 takes precisely the chain isomorphism, differential block and projection assertion stated in the new cone lemma. It takes the cone description of all distinguished homotopy triangles from lem-pur-homotopy-category-triangulated, and inverse rotation and closure under triangle isomorphisms from def-weil-triangulated-category. The third-arrow calculation is explicit: minus projection, the r=-1 shift multiplier, and theta[1] give (-1)*(-1)^(j+1)*(-1)^j=+1. The image triangle is consequently the inverse rotation of the cone triangle of U(f), with all three arrows checked.

Step 5 uses the localization exactness clause of lem-pur-homotopy-category-triangulated. I also read its Mathlib source pointers, including DerivedCategory/Basic.lean:153-175 (coherent shifts and exact Qh). Its source and target are the unbounded homotopy and derived categories for an abelian category, exactly as needed. Composite shift equations and exactness are written out, so no uncited composition theorem is being smuggled in. This existing node is a Mathlib leaf and needs no off-unit route exception. Each quote in citations.json is copied literally from the cited statement, including the needed cone characterization and localization clause.

I checked zero categories, zero complexes and f=0: theta reduces to the displayed biproduct decomposition and the triangle splits. For f=id, t=id and the same coordinate isomorphism applies to the identity cone, with no exactness hypothesis. In characteristic two all signs become 1 and the signed equations still hold. Arbitrarily unbounded inputs cause no infinite sums: each output projection involves two maps, and only integer-indexed products occur. Index and sign assertions were additionally checked by Python integer arithmetic over negative and positive indices (-8 through 8 for coherent shifts, -16 through 16 for boundary and inverse signs). This was not a Lean run or compilation. No new statement assumes injectivity, flatness, exact products, or extra small products.

I reviewed delivery-errors B-E: the new node is self-contained and statement-only; notions have the existing abelian/complex definition dependencies and the products, differential, cone and maps are explicit. Its source uses the actual Stacks tag and label. All non-elementary proof inputs are the new cone isomorphism and existing homotopy/localization theorem, and the triangle axioms; none is borrowed from the proof of a cited node. Searches were run by msearch.py and read, including a second semantic phrasing. mapBifunctorHomologicalComplex builds a bicomplex (Bifunctor.lean:47,84), map₂HomologicalComplex totalizes covariantly (line 302), and mappingCone.mapHomologicalComplexIso (HomotopyCategory/MappingCone.lean:639) applies a termwise covariant functor. None is the stated contravariant product Hom cone isomorphism by one-line specialization. The zero-hit exact bifunctorHom/mappingCone search is also recorded. No new node is elementary, a clause of the item, or a duplicate identified by the DAG/blueprint searches. Every non-elementary step is below 2000 characters; the longest is the explicit triangle assembly. There is no circular use of the item or its Verdier-duality parent. No SGA source is used.

## Not duplicates

lem-sf-signed-bifunctor-cone-iso vs lem-per-bounded-above-rhom-hyperext: the existing statement concerns Finite-diagonal hyper-Ext spectral sequence in the bounded-below second argument; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-per-constructible-ext-filtered-colimit: the existing statement concerns Sheaf Ext from a bounded-above constructible etale complex commutes with filtered colimits; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-per-etale-internal-hom-localization: the existing statement concerns Etale internal Hom localization triangle for arbitrary coefficients; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-per-localization-dual-boundary-pairing: the existing statement concerns The dual localization boundary transposes to evaluation followed by the support boundary; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-per-relative-bidual-triangles: the existing statement concerns Relative evaluation biduality respects distinguished triangles; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-pod-coefficient-dual-perfect: the existing statement concerns Perfectness is preserved by coefficient duality; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-weil-pbc-ringed-complete-element-addition: the existing statement concerns Sum of complete local sections is complete; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-weil-pbc-ringed-complete-element-multiplication: the existing statement concerns Multiples of complete local sections are complete; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-weil-pbc-ringed-derived-complete-elements-ideal: the existing statement concerns Vanishing localizations form an ideal; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-weil-pbc-ringed-internal-hom-exact-restriction: the existing statement concerns Derived internal Hom calculus on small ringed sites; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-weil-pbc-ringed-internal-hom-exact-universes: the existing statement concerns Independent-universe exactness of ringed internal Hom; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-coef-bidual-evaluation-shift-one: the existing statement concerns Degree-one signed shift compatibility of coefficient evaluation; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-coef-etale-hom-thick-locus: the existing statement concerns Triangulated compatibility of the evaluation-defined scalar Hom comparison; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-coef-etale-hom-transpose-exact: the existing statement concerns Reversed exactness of the specified étale Hom transpose; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-coef-rational-bidual-triangle-compatibility: the existing statement concerns Coefficient biduality map is compatible with shifts and triangles; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-coef-rational-retract-evaluation: the existing statement concerns Evaluation on retracts and extension of a perfect pairing; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-coef-signed-derived-internal-hom-exact: the existing statement concerns Normalized exactness of contravariant internal derived Hom; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-sf-bifunctor-homotopy-exact: the item proves coherent triangulatedness after homotopy descent and localization; the new node gives only the explicit chain isomorphism for a single cone, with no such conclusions.

lem-sf-signed-bifunctor-cone-iso vs lem-sf-double-hom-cone-comparison: the existing lemma is double internal sheaf Hom and its covariant cone comparison; the new lemma is a single contravariant product Hom for three arbitrary abelian categories, with a different signed differential.

lem-sf-signed-bifunctor-cone-iso vs lem-sf-etale-generic-exchange-algclosed: the existing statement concerns Geometric-generic closed-support and internal-Hom exchange over arbitrary algebraically closed fields; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-sf-etale-generic-hom-triangle: the existing statement concerns Internal-Hom comparison respects the finite stratification triangles; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-sf-etale-local-dual-interval: the existing statement concerns Uniform local models and Tor interval for a twisted coefficient dual; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-sf-even-line-hom-shift: the existing statement concerns Signed first-variable shift compatibility of the internal-Hom line comparison; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-sf-hom-triangulated: the existing statement concerns Exactness of the internal Hom in each variable; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-sf-localized-bounded-hom-comparison: the existing statement concerns Localized bounded internal-Hom comparison by finite tails; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-sf-rational-thick-evaluation: the existing statement concerns Triangulated closure of the rational evaluation class; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-sf-weil-verdier-dual-triangulated: the existing statement concerns The Verdier dual of Weil complexes is a triangulated functor; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-trf-external-hom-thick-reduction: the existing statement concerns Exactness and shift compatibility for the external Hom thick reduction; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-weil-duality-pairing: the existing statement concerns The duality pairing and the double-dual morphism; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-weil-native-internal-hom-contravariant-exact: the existing statement concerns Coherent contravariant exactness of native derived internal Hom; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs prop-sf-dualizable: the existing statement concerns Perfect complexes are dualizable; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs sk-thm-sf-kunneth-verdier: the existing statement concerns Künneth–Verdier isomorphism; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs thm-coef-integral-verdier: the existing statement concerns Integral Verdier biduality; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs thm-sf-dual-perfect: the existing statement concerns The dual of a perfect complex; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs thm-trf-internal-hom-pullback: the existing statement concerns Internal Hom versus pullback for a site-perfect first variable; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-sfb-constructible-internal-hom-continuity: the existing statement concerns Bounded-below continuity of constructible derived internal Hom; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-sfb-rhom-colimit-cohomology-ladder: the existing statement concerns Exact cohomology ladder for the internal-Hom filtered-colimit comparison; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-sfb-rhom-colimit-source-transport: the existing statement concerns Source-isomorphism and signed-shift transport of the internal-Hom colimit comparison; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-sfb-rhom-continuity-triangle-closure: the existing statement concerns Triangle closure of bounded-target internal-Hom continuity; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-sfb-ringed-complete-triangulated: the existing statement concerns Exact Koszul completion and the triangulated complete locus; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs def-pur-external-rhom-pairing-interface: the existing statement concerns External global Hom evaluation interface; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-pur-external-rhom-cone-pairing: the existing statement concerns External global derived Hom evaluation respects coefficient cones; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-pur-external-rhom-derived-braiding: the existing statement concerns Localization tensor comparison preserves Koszul braiding; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-pur-external-rhom-signed-cones: the existing statement concerns Transport normalized external evaluations to both native coefficient cones; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-pur-supported-exterior-product-boundary: the existing statement concerns Supported exterior products commute with connecting maps in both variables; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-trf-derived-evaluation-canonical-map: the existing statement concerns Canonical derived evaluation morphism and its triangle naturality; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-trf-tensor-double-hom-exact-comparisons: the existing statement concerns Exact tensor and two-target double-Hom functors with specified signed comparisons; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

lem-sf-signed-bifunctor-cone-iso vs lem-zl-lisse-cohomology-derived-dual: the existing statement concerns Cohomology of the coefficient dual of a lisse-cohomology complex; it does not give the new explicit chain isomorphism for the first-variable cone of an arbitrary separately additive H between three abelian categories.

## Unfinished work

No item proof step is left unfinished. The single new statement-only cone comparison is deliberately left unsplit for the next stage-1 item. No Lean files were written and no compiler, Lake or build tool was run. The required delivery dry run and push are performed after this report is written.

## Dry-run repair

The first dry run rejected the shape as a single non-elementary step carrying all content. Step 5 was marked elementary because the composition is a direct application, but it invokes the substantive localization exactness theorem. I conservatively marked this invocation non-elementary. The homotopy and coherent-shift calculations remain explicit in the item, the new lemma remains only a chain-level cone isomorphism, and no statement, citation or proof argument was changed.
