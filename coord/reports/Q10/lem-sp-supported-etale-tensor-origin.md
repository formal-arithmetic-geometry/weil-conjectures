## Worker report

Files written: the existing item dag/nodes/sec-smooth-purity/lem-sp-supported-etale-tensor-origin.json and the following new statement-only nodes (both status unsplit; neither is a Mathlib leaf):

- lem-sp-supported-constructible-origin-comparison: construct a bounded constructible etale origin, extend it by zero, and compare the unbounded coefficient tensor.
- lem-sp-supported-scalar-tor-interval: identify the open-supported coefficient tensor with restricted scalar extension, prove its interval, and reflect the interval to any supplied etale complex.

Attachments: none. The project source search under lean/WeilConjectures found no declaration for the item. Its stage-2 theorem in lean/Sheaf/SecSmoothPurity/SupportedEtaleTensorOrigin.lean:432 ends in sorry at line 455; it is not a finished proof. No Lean was written or compiled.

WANTED: none.

The sandbox contained only dispatcher markers, with no delivered node, report, or searches.jsonl to preserve. I copied the current shared-repository item; its six proof lengths and complete argument agree with the return entry. The repair leaves its statement, original provenance, Lean attachment, and maintainer-owned metadata unchanged. Existing Mathlib searches in the item are retained. New searches are logged by the authorized msearch.py command. No target or unit route was changed, and there is no statement dispute.

## Repair of the return

The return requires actual parallel proof tasks, at least two new unsplit nodes of comparable size, the entire original argument preserved, and an assembly of at most 3000 characters. The two extracted arguments carry old steps 1-3 (2097 characters) and old steps 4-6 (1886 characters), respectively. Both new files contain only self-contained theorem statements, with empty proof and proof_deps and null proof_origin. Neither depends on this item or the other new node; future workers can start both independently. Their statements record the full outputs needed from their allocated arguments. The first has no Tor-amplitude assumption and deliberately makes no boundedness claim about H. The second takes an arbitrary E and a supplied pullback isomorphism, and constructs no etale origin. Thus neither simply renames the item. The assembly only instantiates them, fixes e and r, composes their specified isomorphisms, and reads boundedness as D+.

## Original argument retained and allocated

The following is the returned repository proof verbatim. This preserves every argument for the workers assigned to the two extracted statements; it is not a proof inside either unsplit node.

### Returned step 1 -> lem-sp-supported-constructible-origin-comparison

For every integer q apply [lem-weil-pbc-finite-ring-constructible-sheaf-origin] to the intrinsically constructible A-module sheaf H^q(M). It gives a globally constructible etale A-module sheaf F_q with nu_U^*F_q isomorphic to H^q(M). The ring A is finite and U is an arbitrary scheme, precisely the hypotheses of that node; no Noetherianity of U is used. Since M is bounded, [lem-weil-pbc-fixed-module-bounded-constructible-origin] now gives a bounded etale complex L with globally constructible cohomology and an isomorphism e:nu_U^*L -> M. Fix this witness e for the remaining canonical identifications.

Uses: lem-weil-pbc-finite-ring-constructible-sheaf-origin, lem-weil-pbc-fixed-module-bounded-constructible-origin

Source: {"document": "literature/stacks-project/proetale.tex", "place": "Tags 09AK (lemma-compare-constructible) and 09AL (lemma-compare-constructible-derived); finite-ring global-stratification versions recorded in the cited nodes"}

### Returned step 2 -> lem-sp-supported-constructible-origin-comparison

Set K=j_!^{et,A}L and N=j_!^{pro,A}M. Etale extension by zero is exact by [lem-weil-pbc-extension-by-zero-exact]; pro-etale extension by zero is exact and acts degreewise by [lem-cbc-proetale-extension-zero]. Hence [lem-weil-pbc-exact-functor-complex-cohomology] gives H^q(K)=j_!^{et,A}H^q(L) and H^q(N)=j_!^{pro,A}H^q(M); in particular both are bounded. Apply [lem-cbc-proetale-extension-zero-comparison] degreewise to a representative of L. Its natural sheaf isomorphism is a chain isomorphism, and the exact functors on both sides preserve quasi-isomorphisms, so it gives nu_Z^*K isomorphic to j_!^{pro,A}nu_U^*L. Composing with j_!^{pro,A}(e) gives the required canonical identification nu_Z^*K isomorphic to N.

Uses: lem-weil-pbc-extension-by-zero-exact, lem-cbc-proetale-extension-zero, lem-weil-pbc-exact-functor-complex-cohomology, lem-cbc-proetale-extension-zero-comparison

Source: {"document": "literature/stacks-project/proetale.tex", "place": "Tag 09AF (lemma-jshriek-comparison); exactness from sites-modules.tex Tag 03DJ (lemma-extension-by-zero-exact), cohomology from homology.tex Tag 010N (lemma-exact-functor)"}

### Returned step 3 -> lem-sp-supported-constructible-origin-comparison

Regard the degree-zero constant sheaf B_{Z,et} as an A_{Z,et}-module and put H=K tensor^L_A B_{Z,et}. The constant-ring identification in [lem-sf-comparison-pullback-exact], applied to A and B, identifies nu_Z^*B_{Z,et} with B_Z, including its A-action: the identifications preserve constant sections and therefore the structural map A -> B. Apply [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] to the comparison morphism with the structural ring isomorphism nu_Z^{-1}A_{Z,et} -> A_Z. Its derived pullback is termwise nu_Z^*, since that functor is exact. It gives nu_Z^*H isomorphic to (nu_Z^*K) tensor^L_{A_Z} B_Z, hence to N tensor^L_{A_Z}B_Z by Step 2. This use of the tensor comparison is in the unbounded derived categories; no boundedness of H has yet been asserted.

Uses: lem-sf-comparison-pullback-exact, lem-weil-pbc-ringed-topoi-derived-tensor-pullback

Source: {"document": "literature/stacks-project/sites-cohomology.tex", "place": "Tag 07A4 (lemma-pullback-tensor-product); constant-coefficient exactness as recorded in lem-sf-comparison-pullback-exact"}

### Returned step 4 -> lem-sp-supported-scalar-tor-interval

Choose integers a <= b witnessing the finite Tor amplitude of M. By [def-weil-proetale-tor-amplitude], testing this very interval against the degree-zero A_U-module B_U gives H^q(Q)=0 for q outside [a,b], where Q=M tensor^L_{A_U}B_U is viewed as an A-complex. This tests M against B_U and imposes no flatness or projective-dimension condition on B.

Uses: def-weil-proetale-tor-amplitude

Source: {"document": "literature/stacks-project/sites-cohomology.tex", "place": "Tag 08FZ (definition-tor-amplitude), degree-zero test module B_U"}

### Returned step 5 -> lem-sp-supported-scalar-tor-interval

Apply [lem-cbc-extension-zero-projection-formula] with coefficient ring A, complex M on U and degree-zero complex B_Z on Z. Restriction of B_Z is canonically B_U by [prop-weil-pbc-proetale-constant-ring-map], so N tensor^L_{A_Z}B_Z is canonically j_!^{pro,A}Q. The scalar extension M_B of [det-sp-scalar-extension-functor](1) is computed by P tensor_A B_U for a K-flat representative P of M, with B_U acting on the right factor. Forgetting this B-action leaves exactly the complex computing Q. Thus Q is canonically Res_{A->B}M_B, with the identification induced by the identity on that tensor complex. The restriction-of-scalars compatibility in [lem-cbc-proetale-extension-zero] gives j_!^{pro,A}Q isomorphic to Res_{A->B}j_!^{pro,B}M_B. This proves the second claimed identification. Exactness of that same j_! and the cohomology formula of [lem-weil-pbc-exact-functor-complex-cohomology] show that j_!^{pro,A}Q, and consequently nu_Z^*H by Step 3, have cohomology only in [a,b].

Uses: lem-cbc-extension-zero-projection-formula, prop-weil-pbc-proetale-constant-ring-map, det-sp-scalar-extension-functor, lem-cbc-proetale-extension-zero, lem-weil-pbc-exact-functor-complex-cohomology

Source: {"document": "literature/stacks-project/sites-cohomology.tex", "place": "Tag 0GL1 (lemma-j-shriek-and-tensor); the scalar extension is the K-flat construction in Tag 06YY (lemma-derived-base-change)"}

### Returned step 6 -> lem-sp-supported-scalar-tor-interval

For q outside [a,b], exactness and the cohomology comparison of [lem-sf-comparison-pullback-exact] identify nu_Z^*H^q(H) with H^q(nu_Z^*H)=0 by Step 5. By [det-pe-classical-sheaves-modules], nu_Z^* is faithful on A-module sheaves. Therefore nu_Z^*(id_{H^q(H)})=0 implies id_{H^q(H)}=0, so H^q(H)=0. Thus H is bounded in [a,b]. Together with Step 2, K and H are bounded etale A-complexes and in particular belong to D^+. All identifications were the canonical comparisons followed by the fixed origin witness e; no further choices of isomorphisms were made.

Uses: lem-sf-comparison-pullback-exact, det-pe-classical-sheaves-modules

Source: {"document": "literature/stacks-project/proetale.tex", "place": "Tag 099T (lemma-fully-faithful); exactness/cohomology compatibility as in sites-modules.tex Tag 04JC"}

## Review by Q10

I read the current blueprint det-sp-reduction-direct-image proof, Step 1 (exact open extension and coefficient tensor) and Steps 2-3 (the finite-window inputs), and the unit sk-lem-sp-reduction. I read Stacks proetale.tex labels lemma-compare-constructible (09AK), lemma-compare-constructible-derived (09AL), lemma-jshriek-comparison (09AF), and lemma-fully-faithful (099T); sites-cohomology.tex labels lemma-pullback-tensor-product (07A4), lemma-pullback-K-flat (0G7E), lemma-derived-base-change (06YY), lemma-j-shriek-and-tensor (0GL1), and definition-tor-amplitude (08FZ); sites-modules.tex labels lemma-extension-by-zero-exact (03DJ) and lemma-flat-pullback-exact (04JC); and homology.tex lemma-exact-functor (010N). These are ingredient sources; the simultaneous statements of the new nodes are agent-written combinations, as their source records say. No SGA route is used.

For the first new node, old step 1 uses the finite-ring constructible-sheaf origin equivalence and fixed-module bounded-constructible origin theorem. I opened both cited node statements: the former permits every scheme and finite coefficient ring, and the latter expressly provides bounded L with globally constructible cohomology from the individual cohomology origins. This avoids importing a qcqs or Noetherian scheme hypothesis from a different origin theorem. Old step 2 uses the etale exact-extension theorem and pro-etale exact-extension theorem, each on the appropriate site, and the natural exact-functor/cohomology comparison. The sheaf open-comparison node gives exactly the natural isomorphism on each term; exactness makes both functors preserve quasi-isomorphisms, so that chain isomorphism descends. Old step 3 uses the constant-ring and exactness clauses of lem-sf-comparison-pullback-exact, then the canonical bifunctorial derived tensor isomorphism of lem-weil-pbc-ringed-topoi-derived-tensor-pullback. I checked that its statement works in unbounded categories and with arbitrary ringed-topos pullback, so it does not assume H is already bounded. Constant sections make the comparison compatible with A to B, not just the two rings separately. These outputs are all stated in the first new node, including the normalization relative to e.

For the second new node, old step 4 is the definition of Tor amplitude tested against the degree-zero A-module B_U: the property belongs to M, not to B. Old step 5 uses the open projection theorem on arbitrary complexes, the constant-ring pullback identification j^{-1}B_Z=B_U, scalar extension clause (1), exact pro-etale open extension including its stated scalar-restriction compatibility, and exact-functor/cohomology. I opened all five statements. They give the projection and coefficient action claimed, not merely a definition or a sheaf-level substitute for a derived theorem. On a K-flat P the identity on P tensor_A B identifies Q with the underlying A-complex of M_B; after exact j_! the resulting isomorphism is the one specified by the new statement. Old step 6 uses the exact cohomology comparison and fully faithful module comparison of det-pe-classical-sheaves-modules. These explicitly give faithfulness; applying it to id of each vanished cohomology sheaf reflects zero. The new statement allows arbitrary E with the supplied pullback isomorphism, so no prior bounded-below assumption is smuggled into this reflection.

Assembly step 1 cites only lem-sp-supported-constructible-origin-comparison, whose statement contains the existence of L,e, bounded K,N, c_e and t_e. Its finite-ring and bounded-constructible hypotheses follow verbatim from the item; dropping the unused Tor bound in the extracted task is valid. Assembly step 2 cites only lem-sp-supported-scalar-tor-interval. The item's finite primary rings and finite Tor interval match its hypotheses; E=H and r=t_e satisfy precisely its displayed premise. Its statement supplies the scalar identification and vanishing of H outside the interval, so this citation uses no proof-internal assertion. citations.json quotes literal substrings of these statements. Assembly step 3 is elementary: finitely supported cohomology has a lower bound, hence membership in D+. Both non-elementary assembly steps are under 2000 characters; no long inline comparison is hidden in them.

I checked B-E against the actual files: every object and coefficient action is introduced, the two sites and ordinary derived categories are explicit, and all defining notions have stmt_deps. The new nodes have no proof steps or proof sketches in their statements. Their derived comparisons are isomorphisms in the derived category, not per-degree substitutes. The searches use the whole DAG, the blueprint ancestor and whole-blueprint searches for constructible origin, supported tensor, extension zero tensor, open scalar, and Tor interval, plus the actual Stacks tags. I read candidate statements including lem-sf-comparison-open-tensor-coherence, lem-trf-witnessed-open-pullback, lem-cbc-completed-open-finite-etale-origins, lem-weil-pbc-finite-ring-constructible-derived-origin, lem-exc-comparison-tor-interval, lem-pe-constructible-comparison-tensor-test-reflection, and lem-fix-open-scalar-tensor-normalization. They supply ingredients or have stronger geometric/coefficient hypotheses; none states either complete extracted task. In particular an existing derived tensor comparison by itself does not construct L, and a Tor-interval comparison assuming D+ cannot establish D+ here. The new nodes do not cite each other or their parent, so the extraction adds no cycle. No off-unit theorem is used directly in the assembly.

Small cases: U empty makes N,K,H zero (for the existence witness choose L=0); j identity removes extension by zero without altering either comparison; M=0 has zero origin and tensor; B=0 gives the zero tensor and scalar extension; and A=B=0 is allowed. For a=b the second task is still exactly a single cohomological degree. For the nonflat map Z/ell^2 to F_ell with M=A_U[0], the test tensor is B_U[0] and has interval [0,0], even though B has infinite projective dimension over A; no claim of exact tensoring with arbitrary M is made. Arbitrary schemes and non-quasi-compact opens remain allowed because the cited origin nodes, exactness, comparison, and projection formula impose no missing finite-type or qcqs restriction. These tests expose no statement error.

## Mathlib searches read

For lem-sp-supported-constructible-origin-comparison:

- leanfinder `A bounded constructible proetale complex has a bounded etale origin whose open extension and unbounded coefficient tensor pull back to the corresponding proetale complexes`: OK: 8 hits; AlgebraicGeometry.IsEtale.of_comp, RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial, Algebra.Etale.exists_subalgebra_fg, Algebra.FormallyEtale.comp, Algebra.Etale.comp, AlgebraicGeometry.IsEtale.instHasOfPostcompPropertySchemeMinMorphismPropertyLocallyOfFiniteTypeFormallyUnramified, RingHom.IsStandardSmooth.exists_etale_mvPolynomial, Algebra.FormallyEtale.instForallOfFinite. no match: the returned algebraic etale and scheme-module restriction facts do not construct a pro-etale constructible derived origin or its supported constant-coefficient tensor comparison.
- leanfinder `For an open immersion the etale to proetale derived comparison commutes with extension by zero and derived tensor with a constant finite coefficient ring`: OK: 8 hits; KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, KaehlerDifferential.isBaseChange_of_formallyEtale, Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul, AlgebraicGeometry.IsEtale.of_comp, AlgebraicGeometry.Scheme.Modules.restrictFunctorComp, Algebra.FormallyEtale.of_restrictScalars. no match: the returned algebraic etale and scheme-module restriction facts do not construct a pro-etale constructible derived origin or its supported constant-coefficient tensor comparison.
- leansearch `Exact etale proetale comparison of the derived tensor of an open extension by zero with a constant coefficient module before any boundedness assumption`: OK: 8 hits; AlgebraicGeometry.Scheme.Modules.instIsLeftAdjointRestrictFunctor, Algebra.Etale.formallyEtale, RingHom.Etale, RingHom.Etale.propertyIsLocal, Algebra.FormallyEtale.instTensorProduct, AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale.congr_simp. no match: the returned algebraic etale and scheme-module restriction facts do not construct a pro-etale constructible derived origin or its supported constant-coefficient tensor comparison.
- loogle `"Sheaf", "mapDerivedCategory"`: OK: 0 hits; . no match: the returned algebraic etale and scheme-module restriction facts do not construct a pro-etale constructible derived origin or its supported constant-coefficient tensor comparison.
- grep `pro.?etale.*(tensor|extension)|extension.*pro.?etale`: OK: 0 hits; . no match: the returned algebraic etale and scheme-module restriction facts do not construct a pro-etale constructible derived origin or its supported constant-coefficient tensor comparison.

For lem-sp-supported-scalar-tor-interval:

- leanfinder `An etale complex whose proetale pullback is the coefficient tensor of an open supported finite Tor amplitude complex is bounded in the same interval`: OK: 8 hits; Algebra.FormallyEtale.instTensorProduct, Algebra.etaleLocus_eq_compl_support, Algebra.FormallyEtale.comp, Algebra.FormallyEtale.of_restrictScalars, AlgebraicGeometry.IsEtale.of_comp, Algebra.FormallyEtale.Algebra.FormallyEtale.of_restrictScalars, Algebra.Etale.exists_subalgebra_fg, Algebra.FormallyEtale.instForallOfFinite. no match: complex-shape extension and algebraic etale tensor results do not state geometric open extension, scalar restriction, or reflection of its Tor-test interval through site comparison.
- leanfinder `The derived scalar extension of a finite Tor amplitude complex extended by zero is bounded in the original Tor interval after forgetting scalars`: OK: 8 hits; HomologicalComplex.extend_exactAt, HomologicalComplex.instIsStrictlySupportedExtend, HomologicalComplex.extend_exactAt_iff, HomologicalComplex.extend.instHasHomology, HomologicalComplex.isZero_extend_X, HomologicalComplex.extend.hasHomology, HomologicalComplex.isZero_extend_X', HomologicalComplex.extend.instHasHomologyF. no match: complex-shape extension and algebraic etale tensor results do not state geometric open extension, scalar restriction, or reflection of its Tor-test interval through site comparison.
- leansearch `Extension by zero of a finite Tor amplitude proetale complex after derived scalar extension has the same cohomology bounds without finite projective dimension of coefficients`: OK: 8 hits; HomologicalComplex.extend.d, HomologicalComplex.extendMap_zero, HomologicalComplex.extend.d_none_eq_zero', CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_symm_zero, CategoryTheory.HasExt.instHasSmallLocalizedShiftedHomHomologicalComplexIntUpQuasiIsoOfIsGEOfIsLEOfNat, HomologicalComplex.extend.leftHomologyData.lift_d_comp_eq_zero_iff', HomologicalComplex.extend_single_d, CategoryTheory.instHasProjectiveDimensionLTOfNatNat. no match: complex-shape extension and algebraic etale tensor results do not state geometric open extension, scalar restriction, or reflection of its Tor-test interval through site comparison.
- loogle `"Sheaf", "Tor"`: OK: 12 hits; CategoryTheory.OverPresheafAux.yonedaCollectionFunctor, CategoryTheory.OverPresheafAux.yonedaCollectionFunctor_obj, CategoryTheory.OverPresheafAux.yonedaCollectionFunctor_map, CategoryTheory.CostructuredArrow.overEquivPresheafCostructuredArrow_functor_map_toOverCompYoneda, CategoryTheory.CostructuredArrow.overEquivPresheafCostructuredArrow_functor_map_toOverCompCoyoneda, CategoryTheory.Presheaf.functorToRepresentables, CategoryTheory.Presheaf.instIsLeftKanExtensionOppositeObjFunctorTypeUliftYonedaUliftYonedaMap, CategoryTheory.Presheaf.instIsLeftKanExtensionOppositeObjFunctorTypeYonedaYonedaMap. no match: complex-shape extension and algebraic etale tensor results do not state geometric open extension, scalar restriction, or reflection of its Tor-test interval through site comparison.
- grep `tor.?amplitude|extensionByZero|extension_by_zero|lowerShriek`: OK: 0 hits; . no match: complex-shape extension and algebraic etale tensor results do not state geometric open extension, scalar restriction, or reflection of its Tor-test interval through site comparison.

I read the returned signatures. Scheme.Modules restriction and its stalk comparison concern structure-sheaf modules on the Zariski site; they do not furnish either small-etale/pro-etale derived theorem. ComplexShape.extend concerns extension of an indexing shape, not geometric extension by zero. The returned etale algebra results concern ring morphisms. Loogle returned zero for the mapDerivedCategory query and presheaf categorical hits for the Tor string query, none giving the stated operations. The grep searches found no corresponding geometric open/Tor declarations in Mathlib. Hence neither new statement is an exact match or a one-line specialization.

## Not duplicates

lem-sp-supported-constructible-origin-comparison vs def-coef-semilinear-derived-calculus: The existing statement concerns Ordinary derived semilinear calculus interfaces; the new task additionally constructs a bounded constructible etale origin of arbitrary bounded intrinsically constructible M and gives its supported unbounded coefficient-tensor comparison without any Tor assumption.

lem-sp-supported-constructible-origin-comparison vs lem-sf-site-perfect-opcycles-retract-transport: The existing statement concerns transport slice retract; the new task additionally constructs a bounded constructible etale origin of arbitrary bounded intrinsically constructible M and gives its supported unbounded coefficient-tensor comparison without any Tor assumption.

lem-sp-supported-constructible-origin-comparison vs lem-sf-site-finite-projective-lift: The existing statement concerns exists local lift overMap from finiteFree; the new task additionally constructs a bounded constructible etale origin of arbitrary bounded intrinsically constructible M and gives its supported unbounded coefficient-tensor comparison without any Tor assumption.

lem-sp-supported-constructible-origin-comparison vs lem-sf-open-operation-models: The existing statement concerns Open operation comparisons with fixed tensor models and right square; the new task additionally constructs a bounded constructible etale origin of arbitrary bounded intrinsically constructible M and gives its supported unbounded coefficient-tensor comparison without any Tor assumption.

lem-sp-supported-constructible-origin-comparison vs lem-sf-site-perfect-upper-model: The existing statement concerns exists strictPerfect upper model; the new task additionally constructs a bounded constructible etale origin of arbitrary bounded intrinsically constructible M and gives its supported unbounded coefficient-tensor comparison without any Tor assumption.

lem-sp-supported-constructible-origin-comparison vs lem-sf-site-finite-projective-section: The existing statement concerns exists local section overMap of finiteFree retract; the new task additionally constructs a bounded constructible etale origin of arbitrary bounded intrinsically constructible M and gives its supported unbounded coefficient-tensor comparison without any Tor assumption.

lem-sp-supported-constructible-origin-comparison vs def-sf-integral-open-operations: The existing statement concerns Pinned integral open coefficient and operation presentation; the new task additionally constructs a bounded constructible etale origin of arbitrary bounded intrinsically constructible M and gives its supported unbounded coefficient-tensor comparison without any Tor assumption.

lem-sp-supported-constructible-origin-comparison vs lem-sf-canonical-open-restriction-model: The existing statement concerns Canonical open restriction on augmented quotient models; the new task additionally constructs a bounded constructible etale origin of arbitrary bounded intrinsically constructible M and gives its supported unbounded coefficient-tensor comparison without any Tor assumption.

lem-sp-supported-constructible-origin-comparison vs lem-sf-site-perfect-restriction-exact: The existing statement concerns overFunctor exact ofUniverses; the new task additionally constructs a bounded constructible etale origin of arbitrary bounded intrinsically constructible M and gives its supported unbounded coefficient-tensor comparison without any Tor assumption.

lem-sp-supported-constructible-origin-comparison vs lem-sf-site-perfect-restriction-additive: The existing statement concerns sitePerfectOverFunctor additive; the new task additionally constructs a bounded constructible etale origin of arbitrary bounded intrinsically constructible M and gives its supported unbounded coefficient-tensor comparison without any Tor assumption.

lem-sp-supported-constructible-origin-comparison vs lem-sf-site-perfect-overmap-additive: The existing statement concerns sitePerfectOverMap additive; the new task additionally constructs a bounded constructible etale origin of arbitrary bounded intrinsically constructible M and gives its supported unbounded coefficient-tensor comparison without any Tor assumption.

lem-sp-supported-constructible-origin-comparison vs lem-sf-site-perfect-overmap-comp: The existing statement concerns sitePerfectOverMapComp; the new task additionally constructs a bounded constructible etale origin of arbitrary bounded intrinsically constructible M and gives its supported unbounded coefficient-tensor comparison without any Tor assumption.

lem-sp-supported-scalar-tor-interval vs lem-pe-kflat-roos-representative-invariance: The existing statement concerns K-flat representative invariance of augmented scalar-extension Roos cones; the new task identifies the coefficient tensor of j_!M with restricted B-scalar extension, bounds it in the specified Tor interval, and reflects that interval to an arbitrary etale E supplied only with a pullback isomorphism.

lem-sp-supported-scalar-tor-interval vs lem-pe-two-term-reduction-cohomology: The existing statement concerns Cohomology and quotient maps of a two-term integral coefficient complex; the new task identifies the coefficient tensor of j_!M with restricted B-scalar extension, bounds it in the specified Tor interval, and reflects that interval to an arbitrary etale E supplied only with a pullback isomorphism.

lem-sp-supported-scalar-tor-interval vs lem-pe-restricted-kflat-tensor-identification: The existing statement concerns Restricted scalar-first K-flat tensor models identify derived scalar extensions; the new task identifies the coefficient tensor of j_!M with restricted B-scalar extension, bounds it in the specified Tor interval, and reflects that interval to an arbitrary etale E supplied only with a pullback isomorphism.

lem-sp-supported-scalar-tor-interval vs def-pe-integral-presentation-encoding: The existing statement concerns Specified integral coefficient presentation encoding; the new task identifies the coefficient tensor of j_!M with restricted B-scalar extension, bounds it in the specified Tor interval, and reflects that interval to an arbitrary etale E supplied only with a pullback isomorphism.

lem-sp-supported-scalar-tor-interval vs lem-pe-kflat-scalar-tower-realization: The existing statement concerns K-flat realization of the augmented derived scalar-extension tower; the new task identifies the coefficient tensor of j_!M with restricted B-scalar extension, bounds it in the specified Tor interval, and reflects that interval to an arbitrary etale E supplied only with a pullback isomorphism.

lem-sp-supported-scalar-tor-interval vs lem-pe-integral-reduction-transition-comparison: The existing statement concerns Quotient transitions under normalized integral coefficient comparison; the new task identifies the coefficient tensor of j_!M with restricted B-scalar extension, bounds it in the specified Tor interval, and reflects that interval to an arbitrary etale E supplied only with a pullback isomorphism.

lem-sp-supported-scalar-tor-interval vs lem-pe-integral-normalized-restriction-squares: The existing statement concerns Normalized finite restriction squares for the integral coefficient presentation; the new task identifies the coefficient tensor of j_!M with restricted B-scalar extension, bounds it in the specified Tor interval, and reflects that interval to an arbitrary etale E supplied only with a pullback isomorphism.

lem-sp-supported-scalar-tor-interval vs lem-sbc-derived-scalar-extension-counit-shift: The existing statement concerns Counit-compatible shift structure of derived change of rings on a site; the new task identifies the coefficient tensor of j_!M with restricted B-scalar extension, bounds it in the specified Tor interval, and reflects that interval to an arbitrary etale E supplied only with a pullback isomorphism.

lem-sp-supported-scalar-tor-interval vs lem-sbc-scalar-extension-counit-properties: The existing statement concerns K-flat computation and triangulatedness of a specified scalar-extension counit; the new task identifies the coefficient tensor of j_!M with restricted B-scalar extension, bounds it in the specified Tor interval, and reflects that interval to an arbitrary etale E supplied only with a pullback isomorphism.

lem-sp-supported-scalar-tor-interval vs lem-sbc-derived-coefficient-map-descent: The existing statement concerns Descent of a termwise coefficient map through a resolving counit; the new task identifies the coefficient tensor of j_!M with restricted B-scalar extension, bounds it in the specified Tor interval, and reflects that interval to an arbitrary etale E supplied only with a pullback isomorphism.

lem-sp-supported-scalar-tor-interval vs lem-weil-pbc-scalar-extension-unit-triangles: The existing statement concerns Scalar-extension maps form morphisms of distinguished triangles; the new task identifies the coefficient tensor of j_!M with restricted B-scalar extension, bounds it in the specified Tor interval, and reflects that interval to an arbitrary etale E supplied only with a pullback isomorphism.

lem-sp-supported-scalar-tor-interval vs def-sf-integral-hom-reduction-comparison: The existing statement concerns Canonical integral internal Hom reduction comparison; the new task identifies the coefficient tensor of j_!M with restricted B-scalar extension, bounds it in the specified Tor interval, and reflects that interval to an arbitrary etale E supplied only with a pullback isomorphism.

Additional close candidates checked:

lem-sp-supported-constructible-origin-comparison vs lem-weil-pbc-finite-ring-constructible-derived-origin: that gives the unsupplied etale origin but no open extension or coefficient tensor comparison; it is an ingredient of the extracted multi-step task.

lem-sp-supported-constructible-origin-comparison vs lem-sf-comparison-open-tensor-coherence: that assumes etale inputs K,N and asserts equality of two comparison paths; it does not construct a bounded constructible origin for intrinsic M.

lem-sp-supported-constructible-origin-comparison vs lem-trf-witnessed-open-pullback: that requires a supplied bounded-below witness and finite-type schemes over the fixed field with DVR-quotient coefficients; the new task constructs the witness for arbitrary schemes and finite rings and includes its unbounded coefficient tensor.

lem-sp-supported-constructible-origin-comparison vs lem-cbc-completed-open-finite-etale-origins: that concerns quotient reductions of completed coefficient objects and presupposes their origins; the new task is ordinary finite coefficients and constructs bounded constructible origin.

lem-sp-supported-scalar-tor-interval vs lem-exc-comparison-tor-interval: that compares Tor amplitude of a pre-existing bounded-below etale complex and its pullback; here E is unbounded a priori, the interval is a cohomological bound for a single coefficient tensor, and the open/scalar comparison is also required.

lem-sp-supported-scalar-tor-interval vs lem-fix-open-scalar-tensor-normalization: that gives scalar/open/tensor coherence, not the finite Tor-test interval or its reflection to arbitrary E.

## Completion

All returned argument blocks have allocated independent tasks; the parent statement is unchanged. No mathematical work was left unfinished within this one-level split. The new statements intentionally remain unsplit for parallel future workers. Required server dry run and delivery results are recorded below after execution.

## Further tag-collision review after first dry run

The dry run also listed the following same-tag candidates. I opened their statements and found these distinct conclusions; they are not substitutes for either extracted task.

lem-sp-supported-constructible-origin-comparison vs lem-weil-pbc-site-extension-by-zero-exact: the existing node states exact extension for abelian sheaves on a localized site, not constructible origin or tensor/site comparison.

lem-sp-supported-constructible-origin-comparison vs lem-weil-pbc-site-restriction-exact: the existing node states exact slice restriction of abelian sheaves, not existence of etale origins or coefficient tensors.

lem-sp-supported-constructible-origin-comparison vs lem-weil-pbc-site-restriction-injectives: the existing node states the ordinary slice adjunction and exactness, without a constructible derived origin or its tensor comparison.

lem-sp-supported-constructible-origin-comparison vs new-over-pullback-adjunction-mono: the existing node states a left adjoint preserving monomorphisms for slice pullback of abelian sheaves, without either derived origin construction.

lem-sp-supported-constructible-origin-comparison vs new-over-pullback-preserves-injectives: the existing node states preservation of injectives by abelian slice restriction, not etale/pro-etale constructible origin.

lem-sp-supported-constructible-origin-comparison vs def-a1-finite-adic-open-section-data: the existing node states an operation-data definition for quasi-compact opens over the finite field with adic coefficients, not an existence theorem for arbitrary schemes and finite rings.

lem-sp-supported-constructible-origin-comparison vs lem-pc-inverse-image-open-free-sheaf: the existing node states inverse image of represented free abelian sheaves on Zariski opens, not small etale/pro-etale constructible complexes.

lem-sp-supported-constructible-origin-comparison vs lem-pc-open-embedding-sheaf-pullback-injectives: the existing node states pullback preserving injective abelian sheaves on topological spaces, not the stated origin and tensor comparison.

lem-sp-supported-constructible-origin-comparison vs lem-pc-open-free-restriction-hom: the existing node states a Hom bijection from a represented open free abelian sheaf on the Zariski site, without constructible origins.

lem-sp-supported-constructible-origin-comparison vs lem-pc-open-inverse-image-injectives: the existing node states preservation of injective abelian sheaves under Zariski open inverse image, not a comparison between the two small sites.

lem-sp-supported-constructible-origin-comparison vs lem-pc-open-restriction-ext-bijective: the existing node states Ext restriction bijections for independently chosen Zariski sheaf isomorphisms, not construction of L or its coefficient tensor.

lem-sp-supported-constructible-origin-comparison vs new-open-embedding-sheaf-pullback-adjunction: the existing node states a mono-preserving left adjoint of topological abelian sheaf pullback, not bounded constructible etale origin.

lem-sp-supported-scalar-tor-interval vs def-a1-integral-completed-tower-pullback-universes: the existing node states a definition of completed integral strict-tower pullback and reduction, not finite constant-ring open tensor bounds.

lem-sp-supported-scalar-tor-interval vs def-per-scalar-extension-unit: the existing node states a normalized scalar unit for the identity ring map, with no claim for arbitrary coefficient maps or Tor bounds.

lem-sp-supported-scalar-tor-interval vs lem-per-proetale-scalar-slice-comparison: the existing node states scalar extension commuting with literal slice restriction, not open extension by zero or reflection of a supported Tor-test interval.

lem-sp-supported-scalar-tor-interval vs lem-pod-derived-reduction-sheaf-resolution-independence: the existing node states naturality and resolution independence of a principal-quotient exact-sections comparison, without its invertibility or open-support bounds.

lem-sp-supported-scalar-tor-interval vs lem-pod-point-sections-derived-reduction-cone: the existing node states the mapping-cone model for integral point reduction, not arbitrary finite rings and open supports.

lem-sp-supported-scalar-tor-interval vs lem-pod-point-sections-derived-reduction-homology: the existing node states the homology comparison for point integral reduction, without an arbitrary open immersion or faithful-comparison reflection.

lem-sp-supported-scalar-tor-interval vs lem-pod-point-sections-derived-reduction-iso: the existing node states the natural isomorphism for point integral reduction, not the supported coefficient tensor interval.

lem-sp-supported-scalar-tor-interval vs lem-pod-principal-derived-tensor-cone: the existing node states the cone model for a regular principal ring quotient, whereas B here can have infinite projective dimension and the conclusion concerns open support and an etale witness.

lem-sp-supported-scalar-tor-interval vs lem-pod-principal-quotient-quasi-iso: the existing node states quotient tensor preserving a quasi-isomorphism when multiplication is termwise injective, not a bound from the Tor interval of M.

lem-sp-supported-scalar-tor-interval vs lem-pod-principal-reduction-comparison: the existing node states a principal-quotient comparison under exact global sections and a domain hypothesis, without open support or interval reflection.

lem-sp-supported-scalar-tor-interval vs lem-pod-principal-reduction-flat-comparison: the existing node states invertibility of the principal-quotient exact-sections comparison on K-flat models, not supported scalar interval bounds.

lem-sp-supported-scalar-tor-interval vs lem-pod-scalar-reduction-cochain-comparison: the existing node states agreement of a chosen completed-to-finite cochain scalar model with prescribed reduction, not a Tor interval bound or its reflection.

The first dry run exited before server preflight because these same-tag distinctions had not been recorded for the server clone ordering. The report now records each requested pair after reading the statements; no new node was replaced because none states either complete extracted argument.

The second dry run required a longer literal citation quote (the bounded-K,N sentence has fewer than 40 characters). citations.json now quotes the complete relevant conclusions, including all comparisons and interval reflection, so every assertion taken by each assembly step is visible in its quote.

Final required dry run: deliver.py Q10 lem-sp-supported-etale-tensor-origin --no-push exited 0 and printed OK (not pushed) at 6be70589706, with server preflight passed. Both new nodes remain status unsplit, neither is a Mathlib leaf, and the assembly has 1174 proof-text characters.
