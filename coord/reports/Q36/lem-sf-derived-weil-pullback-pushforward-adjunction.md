# Worker report

1. Files written:

- dag/nodes/sec-six-functors/lem-sf-derived-weil-pullback-pushforward-adjunction.json: unchanged statement and statement dependencies, three assembly steps, 1855 proof-text characters; no Mathlib match.
- dag/nodes/sec-six-functors/lem-sf-native-weil-injective-adjunction-model.json: new statement, status unsplit, no proof steps; no Mathlib match. Native abelian Weil adjunction and its K-injective computational model.
- dag/nodes/sec-six-functors/lem-sf-native-weil-derived-hom-comparison.json: new statement, status unsplit, no proof steps; no Mathlib match. The normalized Hom composite, resolution independence, naturality and identity transposes.
- citations.json: every citation in the three assembly steps, with literal statement quotations.

2. Attachments: none. The return explicitly forbids another ATTACH disposition. I followed the released stage-1 keep_plan repair order and did not treat previously reviewed status as completion of the repair.

3. WANTED: none. The current blueprint, native source and Stacks sources used are present.

4. The returned nine-step proof had 7580 characters. Its mathematics and statement are retained. The repair changes its work distribution: two substantial, comparable statement-only obligations now carry the native model and the Hom-comparison argument, while the item applies them, calculates the two triangles, and restricts to the full bounded constructible categories. Neither new node states the restricted adjunction, and neither asserts the whole original conclusion. The first does not assert a derived Hom bijection; the second does not establish its native underived hypotheses or any constructible preservation. Both remain open for separate workers.

5. Nothing required for this one-level split remains unfinished. Proofs of the two explicitly unsplit nodes are intentionally queued. There was no retained sandbox node, report or search log at continuation: only dispatcher marker files existed. I checked for an active delivery for this exact item before writing or running a delivery; there was none. I recovered the nine-step proof from the current shared node, which is the reviewed version of the returned head fb9ac2d622252ecff0be773f09a125cd5ecce345. Its two maintainer additions concerning def-sfb-right-derived-functor and the comparison-unit equation are retained explicitly in the new statements. The packaging tool rebases the delivery onto the current server state. No git command was run in the shared repository and no Lean, compiler, Lake or build was run.

## Current source and provenance

Read the chapter record sec-six-functors and the item's actual unit sk-prop-sf-biduality-general, as well as sk-thm-sf-package and the current main-20261015 fix-lem-tensor-adjunction.proof.md. The relevant blueprint occurrence is the last Hom bijection of Step 1. The item's seeded blueprint ancestor is null: blueprint_refs.py ancestor prints None. I retained that value, the inherited via chain, and a precise from.place; the two children add the item to that via chain. No chapter or unit route is changed. The unit's inherited historical bibliography mentions an excluded source; none is used as a proof source here. The actual route is the native abelian Weil model, Stacks K-injective results, and full-subcategory restriction.

The earlier report's claim that Localization.lean and both Weil derived adjunction declarations were absent is no longer true in the current read clone. I read Localization.lean:175-195, UpperStarLowerStarAdjunction.lean:99-125, Category.lean:128-150,437-460, Adic/Module.lean:117-178, Adic/GeometricFrobenius.lean:82-105, and Endofunctor/IsoAlgebraAdjunction.lean:86-125. The current source has those constructions, but a source-level wrapper with no literal sorry does not certify its transitive closure; the explicit repair instruction requires this split and says not to repeat ATTACH. No new lean_audit closure claim is made. The item's inherited source.place and reviewed record are historical metadata, retained unchanged rather than rewritten as a new attachment claim.

Read Stacks derived.tex Tag 08BJ (lemma-adjoint-preserve-K-injectives) and Tag 070I (lemma-K-injective), including their proofs, and injectives.tex Tags 079Q (remark-existence-D) and 079P (theorem-K-injective-embedding-grothendieck). The tag-to-label correspondences were checked against literature/stacks-project/tags/tags. These supply respectively exact-left-adjoint preservation, localization Hom bijectivity, ringed-site Grothendieckness and existence of K-injective resolutions. Naturality and normalization of the specified native composite are honestly an agent expansion, as in the returned proof, not attributed as a verbatim Stacks theorem.

## Obligation map of the unchanged argument

| Old step | New location | Retained mathematical content |
|---|---|---|
| 1 | injective-adjunction-model | B-module-object/sheaf-module equivalence, Grothendieck A and W, additive Frobenius autoequivalence, exact conservative forgetting, K-injective resolutions in W itself, size convention |
| 2 | injective-adjunction-model | actual ringed-module adjunction lifted through its specified mate comparisons, carrier units and counits, additivity, exactness of the native left adjoint |
| 3 | injective-adjunction-model | termwise homotopy adjunction and both formulas, preservation of K-injectives by G_0, actual right-derived pushforward with its comparison, exact termwise derived pullback |
| 4 | derived-hom-comparison | full displayed four-arrow Hom composite including postcomposition by the resolution and final canonical right-derived computation isomorphism, bijectivity and equivariant extension morphisms |
| 5 | derived-hom-comparison | naturality under every derived source morphism, including inverses of localized quasi-isomorphisms |
| 6 | derived-hom-comparison, and model's comparison equation | unique homotopy representatives of target arrows, comparison naturality equation, resolution-independence via the identity comparison and its homotopy inverse, naturality in the target |
| 7 | derived-hom-comparison | formulas for the two identity transposes with the actual beta and c_r computation isomorphisms; no arbitrary adjunction structure substituted |
| 8 | item assembly step 2 | both explicit triangle calculations from naturality and inverse Hom maps |
| 9 | item assembly step 3 | original full-subcategory restriction text, preservation hypothesis and identification of all Hom sets and maps |

The complete original argument is retained verbatim below. New node statements specify the mathematical obligations rather than embedding a proof or assigning proof steps to an unsplit child. The displayed c_r and target-morphism equations make explicit the canonical identifications already used in the old argument. The two child statements have approximately 2700 and 3000 characters, and the old-work division is steps 1-3 versus 4-7; neither child absorbs the entire proof.

## Searches

Before writing either child, searched the whole DAG for native Weil, K-injectives, fixed pairs, exact/derived adjunctions, the four Stacks tags, and resolution independence, and ran blueprint_refs.py search with K-injective, fixed-pair, resolution-independent, derived adjoint and Weil/adjunction terms. Read the close existing statements, including native-weil-constructible-abelian, native-adic-pullback-frobenius-mates, fixed-pair-adjunction-lift, fixed-pair-derived-forget-comparison, the three generic homotopy/K-injective nodes, kinjective-total-derived, pc-derived-adjoint-functors, sp-exact-pullback-derived-adjunction, sp-canonical-right-derived-adjunction-shift and sbc-unbounded-exact-adjunction-square. The exact proposed ids were also checked absent in the shared DAG. These facts are reused as existing inputs to the future child proofs, not recreated as independent generic lemmas.

Ran ten searches through the mandatory batch2/msearch.py command; their exact queries and raw digest records are in searches.jsonl, and each child records its own two LeanFinder phrasings, LeanSearch query, Loogle query, and Mathlib grep. Both service phrasings were read. No service was unavailable. Ordinary sheaf-module adjunction hits do not state native Frobenius lifting or exactness. The second family returned ordinary nth right-derived-functor naturality, generic derived adjunction and generic K-injective Hom bijectivity. I read Mathlib CategoryTheory/Functor/Derived/Adjunction.lean:37-150, in particular derivedη_fac_app:103 and derivedε_fac_app:125: its abstract derived adjunction assumes left/right derivability plus the two composition derivability hypotheses, none supplied merely by the normalization clause. The child explicitly constructs and compares a particular Hom chain on actual native Weil resolutions; it is not a one-line invocation of that API. The generic Qh_map_bijective hit gives only one arrow in the chain and is already the subject of an existing DAG node. Read SheafOfModules pullbackPushforwardAdjunction at PullbackContinuous.lean:60 and the ordinary module construction; it does not assert native fixed-pair or K-injective claims. The item retains all inherited searches exactly and appends the searches run in this repair.

## Review by Q36

I checked the return against the files and sources, not just proof length. The item statement and stmt_deps match the current repository byte for byte. The two new nodes have self-contained finite-field, coefficient, geometric and size assumptions, actual native categories supplied by the framework, all notion dependencies, precise sources and blueprint places, no proof steps, empty proof_deps and status unsplit. No theorem about ordinary underlying sheaves or fixed pairs in D is substituted for a theorem in D(W).

For assembly step 1 I opened both child statements. The model node explicitly gives Grothendieck W, K-injective resolutions inside W, exact F_0, the actual underived adjunction with carrier maps, preservation by G_0, and the universal right-derived comparison. The comparison node explicitly assumes exactly that model and gives the displayed natural, choice-independent Hom bijection and normalized transposes. The item's finite-field and separated finite-type assumptions give every hypothesis of both children. No boundedness or properness is needed for their ambient conclusions. The first node is a native prerequisite, the second a distinct localization-comparison argument; the assembly does not ask the second node to prove the restricted target.

For assembly step 2 I checked the precise formulas in the comparison node and the two naturality equations. Defining eta by the forward transpose of identity and epsilon by its inverse gives Phi(h)=Rf_*(h) eta and Phi^{-1}(a)=epsilon f^*(a). Putting h=epsilon and a=eta yields the written triangles. This is an elementary two-substitution argument; no extra theorem is hidden under a label of elementary. The identity normalizations use c_s in the unit and f^*(beta_I) in the counit, with the correct domain directions. We do not forget the universal comparison of def-sfb-right-derived-functor.

For assembly step 3 I reread the existing preservation and framework statements. The former is explicitly for the same finite field, prime and separated finite-type maps and says both f^* and Rf_* preserve bounded constructible cohomology. The latter explicitly says the category is a full subcategory of the actual D(W) and defines these restricted functors. Thus both Hom sets, every unit/counit component and both triangle equalities restrict exactly as claimed. The old step 9 is copied unchanged. citations.json quotes literal parts of all five cited statement occurrences; the full statements are included so no premise is concealed by a clipped quotation.

I also reopened the old proof's cited nodes: ring-sheaves-grothendieck applies to arbitrary sheaves of rings on small sites; fixed-pair-derived-forget-comparison explicitly provides Grothendieckness and exact conservative forgetting; native-adic-pullback-frobenius-mates uses ordinary composition and matches the diagrammatic convention of fixed-pair-adjunction-lift; termwise-adjunction-homotopy includes the forward and inverse Hom formulas; right-adjoint-preserves-kinjective assumes exactly an additive adjunction with exact left adjoint; kinjective-hom-derived supplies full bijectivity, not merely injectivity; right-derived-functor supplies the actual universal comparison and its naturality; grothendieck-k-injective supplies existence. These are the inputs whose arguments remain in the extracted obligations, not unmentioned assertions silently removed in the repair.

Small cases checked: for the identity morphism, the lifted adjunction and all computation formulas reduce to the identity adjunction under the chosen resolution isomorphisms. For the empty source both relevant Hom sets are singleton sets and all triangle maps on the source are the unique identities of zero objects. Zero complexes satisfy all formulas. For a point with nontrivial unipotent Frobenius, the category is still D(W); its equivariant extension classes are retained by the K-injective Hom chain. There is no false assumption that G_0 is exact, that Frobenius has finite order on a sheaf, or that forgetting alone computes equivariant Ext. The right-adjoint K-injective statement needs exact F_0, which the first child expressly includes.

Delivery-errors B-E: the children are complete mathematical statements, not new definitions or abbreviated tags; all actual Mathlib searches are recorded without invented queries; the duplicate exclusions are listed below; the assembly's every non-elementary assertion is a cited statement; citations quote statements rather than their proofs; no dependencies cycle back to the item; the children do not simply partition the target's clauses but isolate underived native-model work and independent derived Hom normalization. All three assembly steps are below 2000 characters and total below 3000. Generic off-unit tools remain only in the preserved old argument/future child work, and the present assembly cites same-unit nodes plus the existing framework. No source on the excluded SGA routes is used.

## Not duplicates

lem-sf-native-weil-injective-adjunction-model vs def-coef-hom-representative-evaluation: the existing statement is about Canonical evaluation on fixed Hom representatives (its stated setting begins Let $J$ be a site on a category with object universe $c$ and morphism universe $v$, and let $A$ be a); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs def-coef-hom-zero-cycle-class: the existing statement is about Canonical zero-cycle class in derived global Hom (its stated setting begins Let $J$ be a ringed site, with module sheaves [def-weil-sheaf-of-modules-category], derived category); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs def-coef-ringed-sequence-site: the existing statement is about Canonical ringed sequence site for the coefficient quotient tower (its stated setting begins Fix a prime $\ell$, a finite extension $E/\mathbf Q_\ell$ with its valuation ring and uniformizer [d); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs def-pc-open-module-derived-sections: the existing statement is about Unbounded derived sections of modules over an open (its stated setting begins Let $(X,\mathcal O_X)$ be a ringed space and $U\subseteq X$ open. The category $\operatorname{Mod}(\); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs def-pur-derived-internal-hom: the existing statement is about Derived internal Hom on a ringed site (its stated setting begins Let $\mathcal C$ be a site whose underlying category is small and $\mathcal O$ a sheaf of commutativ); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs def-weil-pbc-koszul-reconstruction-models: the existing statement is about The fixed Koszul and quotient reconstruction models (its stated setting begins For the completed coefficient datum [def-weil-pbc-adic-coefficient-datum], retain the actual module ); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs det-lem-formal-closed-support-derived: the existing statement is about Sections with support: derived adjunction and fiber formula (its stated setting begins In the situation of [det-lem-formal-closed-support-sheaves], let $R\underline\Gamma_Z\colon\D(X_{\ma); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs det-pe-products-derived: the existing statement is about Products in the derived category are termwise (its stated setting begins Let $\mathcal R$ be a sheaf of rings on $X_{\mathrm{proét}}$ and let $(K_i)_{i\in I}$ be a family of); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs det-pe-wc-sections-derived: the existing statement is about Derived sections over a w-contractible affine (its stated setting begins Let $U$ and $\mathcal R$ be as in [det-pe-wc-sections-exact], and let $K$ be an arbitrary (possibly ); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-cbc-constant-derived-limit-resolution-unit: the existing statement is about Projection-defined constant-tower derived-limit unit (its stated setting begins Let $T$ be a scheme and $A,I,A_T$ an adic coefficient datum [def-weil-pbc-adic-coefficient-datum]. P); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-coef-constant-tower-roos: the existing statement is about Canonical Roos triangle of a completed-coefficient derived tower (its stated setting begins Fix a prime l, a finite extension E of Q_l, a scheme W, and the auxiliary datum D with l different f); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-coef-derived-system-evaluation-calculus: the existing statement is about Coherent derived reduction, limit adjunction and fiberwise evaluation (its stated setting begins Fix a prime $\ell$, a finite extension $E/\mathbf Q_\ell$, its valuation ring $R=\mathcal O_E$, a un); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-coef-finite-adjunction-diagram-realization: the existing statement is about Finite exceptional operations and enriched adjunction on coherent coefficient systems (its stated setting begins Fix the global finite-field datum $k=\overline{\mathbf F}_q$ of characteristic $p$ [def-weil-finite-); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-coef-semilinear-derived-sections: the existing statement is about Derived semilinear sections and coefficient-linear geometric operations (its stated setting begins Let $\mathcal C$ be a small site [def-weil-pbc-sites-and-cohomology] and let $B_1\leftarrow B_2\left); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-coef-sequence-sections-limit-comparison: the existing statement is about Derived sections and total limit with specified projections (its stated setting begins Let $\mathcal C$ be a small site [def-weil-pbc-sites-and-cohomology] and $B_1\leftarrow B_2\leftarro); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-exc-proetale-derived-open-restriction: the existing statement is about Unbounded pro-etale direct image commutes with open restriction (its stated setting begins Let $A$ be a finite commutative ring and $p:V\to T$ a morphism of schemes [def-pc-scheme]. Let $i:W\); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-pc-derived-adjoint-functors: assumes ind/pro-system derived-functor existence and asserts a canonical adjunction; it does not identify the native fixed-pair model, its universal K-injective computation maps, or the concrete Hom-chain normalization.

lem-sf-native-weil-injective-adjunction-model vs lem-pc-derived-hom-pushforward-kflat-model: the existing statement is about Derived Hom pushforward on fixed K-flat and K-injective representatives (its stated setting begins Let i:Z -> Y be a morphism of schemes [def-pc-scheme], with any supplied derived category D(O_Y) [de); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-pc-ringed-space-derived-products: the existing statement is about The derived category of modules on a ringed space has products (its stated setting begins Let $(X,\mathcal O_X)$ be a ringed space [def-sc-ringed-space-module-cohomology] and let $D(\mathcal); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-pd-section-derived-pushpull-normalization: the existing statement is about Section equivalence and canonical derived push-pull adjunctions (its stated setting begins Let $\Lambda$ be a commutative condensed ring [sk-def-sfb-condensed-ring], let $f:X\to Y$ be a morph); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-pur-comparison-global-resolution-model: the existing statement is about Resolution model for normalized global site comparison (its stated setting begins Let $\Lambda$ be a finite discrete commutative ring. Use small representatives of the small etale an); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-pur-kinjective-degreewise-existence: the existing statement is about Functorial K-injective resolutions with injective terms (its stated setting begins Let $\mathcal A$ be a Grothendieck abelian category [def-sp-grothendieck-abelian] and $\mathsf{Cpx}(); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-pur-unbounded-derived-boundary: the existing statement is about Unique normalized unbounded derived boundary (its stated setting begins Let C be Grothendieck abelian and D abelian, both with derived categories. Let S be a short complex ); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-pur-unbounded-injective-model: the existing statement is about Unbounded termwise injective K-injective models (its stated setting begins Let C be a Grothendieck abelian category with its derived category. Every object M of D(C) is isomor); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-sbc-unbounded-exact-adjunction-square: works on ordinary ringed-site modules and strict towers, and assumes the canonical unbounded derived adjunction; it does not construct or normalize the native Weil fixed-pair Hom chain.

lem-sf-native-weil-injective-adjunction-model vs lem-sc-bounded-below-injective-resolution: the existing statement is about Bounded-below complexes admit bounded-below K-injective resolutions (its stated setting begins Let $(U,\mathcal O_U)$ be a ringed site with small underlying category, and let $\mathcal G^\bullet$); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-sf-fixed-pair-adjunction-lift: assumes abstract mate-compatible comparisons and proves only an underived fixed-pair adjunction; the model additionally specializes the actual native coefficient model and carries out its derived computation; the Hom node starts after that.

lem-sf-native-weil-injective-adjunction-model vs lem-sf-fixed-pair-derived-forget-comparison: concerns Grothendieckness and forgetting a derived lift; it does not provide this native inverse/direct-image pair or this Hom chain.

lem-sf-native-weil-injective-adjunction-model vs lem-sf-native-adic-pullback-frobenius-mates: supplies the underlying module comparison mate identity and exactness before lifting; it does not give the abelian Weil lift, its K-injective derived computation or normalized ambient Hom chain.

lem-sf-native-weil-injective-adjunction-model vs lem-sf-native-weil-constructible-abelian: covers Grothendieckness, exact conservative forgetting and constructible abelian closure; the new model adds the actual adjunction and its K-injective computation, and the Hom node concerns transposition, not abelian closure.

lem-sf-native-weil-injective-adjunction-model vs lem-sfb-exact-postcomposition-kinjective-descent: the existing statement is about K-injective descent of comparisons after arbitrary exact functors (its stated setting begins Let $\mathcal A_0,\mathcal A_1,\mathcal B$ be abelian categories [def-sp-abelian] with ordinary unbo); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-sfb-galois-kinjective-section-model: the existing statement is about Exact singleton evaluation and K-injective Galois section model (its stated setting begins Let $k$ be a field, $k^s/k$ a separable closure [def-pd-separable-closure], $s=\operatorname{Spec}k$); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-sfb-integral-quotient-section-mate-realization: the existing statement is about Integral quotient scalar and geometric mate realization in section modules (its stated setting begins Fix a prime $\ell$, a finite extension $E/\mathbf Q_\ell$, its valuation ring $A=\mathcal O_E$, a un); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-sfb-kinjective-direct-image-open-word-model: the existing statement is about Simultaneous K-injective models and diagram descent for direct-image/open words (its stated setting begins Let $\Lambda$ be a commutative condensed ring [sk-def-sfb-condensed-ring]. On small representatives ); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-sfb-topos-finite-free-counit-comparison: the existing statement is about Finite-free counit comparison on arbitrary sheaf topoi in specified coordinates (its stated setting begins Let $h:\mathscr X\to\mathscr Y$ be a morphism of sheaf topoi on sites small in the module universe [); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-sp-canonical-right-derived-adjunction-shift: proves canonical shift compatibility of an already available derived adjunction; it states neither the native model nor the detailed Hom-resolution comparison.

lem-sf-native-weil-injective-adjunction-model vs lem-sp-exact-pullback-derived-adjunction: has ordinary ringed-site module categories and K-flat source normalization; the native fixed-pair categories, their exact lifted pair, and the all-complex Hom chain with comparison-independence are not its statement.

lem-sf-native-weil-injective-adjunction-model vs lem-trf-proetale-unit-leray-chain-formula: the existing statement is about Chain representative for ordinary pro-etale module cohomology pullback (its stated setting begins Let $h:X\to Y$ be a morphism of schemes [def-pc-scheme], and let $A$ be a finite commutative ring. U); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-weil-derived-limit-existence: the existing statement is about Existence and computation of derived limits (its stated setting begins Let $\mathcal D$ be a triangulated category and let $(K_n,f_n)$ be an inverse system of objects of $); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-weil-pbc-flat-scalar-tower-limit-square: the existing statement is about Flat scalar restriction and the normalized direct-image strict-limit square (its stated setting begins Let $u:\mathscr U\to\mathscr V$ be a geometric morphism of topoi presented by small sites, meaning $); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-weil-pbc-kinjective-functorial-existence: the existing statement is about Functorial K-injective replacement (its stated setting begins Let $\mathcal A$ be a Grothendieck abelian category [def-sp-grothendieck-abelian] and $\mathsf{Cpx}(); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-weil-pbc-kinjective-hom-derived: gives only localization Hom bijectivity into one K-injective target; the new statements construct the native model or compare its whole derived transposition.

lem-sf-native-weil-injective-adjunction-model vs lem-weil-pbc-kinjective-pullback-abutment: the existing statement is about K-injective representative of the unit--Leray abutment map (its stated setting begins Let $f:Y\to X$ be a scheme morphism, $K,L$ arbitrary complexes of abelian étale sheaves on $X,Y$ [de); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-weil-pbc-kinjective-unit-leray: the existing statement is about Unit--Leray computation on K-injective complexes (its stated setting begins Let $f:Y\to X$ be a scheme morphism [def-weil-pbc-scheme-conventions]. Let $I,J$ be K-injective coch); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-weil-pbc-qcqs-higher-direct-image: the existing statement is about Higher direct images for quasi-compact quasi-separated morphisms (its stated setting begins Let $u:U\to V$ be a quasi-compact and quasi-separated morphism [def-weil-pbc-scheme-conventions] of ); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-weil-pbc-right-adjoint-preserves-kinjective: gives only preservation for a supplied exact-left-adjoint pair; it supplies neither the native pair and its derived model nor the resolution-independent normalized Hom chain.

lem-sf-native-weil-injective-adjunction-model vs lem-weil-pbc-ring-sheaves-grothendieck: asserts Grothendieckness of ordinary module sheaves only; no native Frobenius adjunction, derived model or Hom normalization is included.

lem-sf-native-weil-injective-adjunction-model vs lem-weil-pbc-sequential-tower-evaluation-full: the existing statement is about Compatible derived evaluations lift to a strict derived tower map (its stated setting begins Let $\mathcal C$ be a small site and $R$ a sheaf of rings. Set $\mathcal A=\operatorname{Mod}(R)$ [d); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-weil-pbc-small-module-diagrams-grothendieck: the existing statement is about Small diagrams of module sheaves form a Grothendieck category (its stated setting begins Let $\mathcal C$ be a small site (small in a universe containing the values of all sheaves), let $\m); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs lem-weil-pbc-termwise-adjunction-homotopy: states only the termwise/homotopy adjunction for a supplied additive adjunction; it neither constructs the native abelian adjunction and its K-injective model nor proves this specified derived Hom composite and normalization.

lem-sf-native-weil-injective-adjunction-model vs prop-pur-kinjective-resolutions-exist: the existing statement is about Existence of K-injective resolutions of sheaves of modules (its stated setting begins Let $\mathcal C$ be a site whose underlying category is small (its objects form a set) and $\mathcal); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs prop-weil-pbc-derived-inverse-limit-computation: the existing statement is about Computation of the sequential derived inverse limit (its stated setting begins Let $\operatorname{Tow}_{A}(T)$ be the tower category of [def-weil-pbc-adic-coefficient-datum] and l); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs prop-weil-pbc-kinjective-resolutions-exist: the existing statement is about Existence of K-injective resolutions (its stated setting begins Every complex in $\mathsf{Cpx}(\Mod(T_{\Et},R))$ admits a K-injective resolution $K\to I$, functoria); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-injective-adjunction-model vs prop-weil-pbc-rlim-functoriality: the existing statement is about Functoriality of the sequential derived inverse limit (its stated setting begins Let $\operatorname{Tow}_{A}(T)$ be the tower category of [def-weil-pbc-adic-coefficient-datum], an a); it does not state the native Frobenius fixed-pair inverse/direct-image construction and its specified K-injective computation.

lem-sf-native-weil-derived-hom-comparison vs lem-a1-total-limit-shift-resolution-change: the existing statement is about Termwise limit shifts agree across all K-injective tower resolutions (its stated setting begins Let $\mathcal C$ be a site small in the module universe, $R$ a sheaf of commutative rings, $\mathcal); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-cbc-kinjective-derived-mapping-complex: the existing statement is about K-injective targets compute enhanced derived mapping complexes (its stated setting begins Fix universes as in [def-weil-size-convention]. Let $E$ be a small category, $\Lambda$ a commutative); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-exc-proetale-derived-open-restriction: the existing statement is about Unbounded pro-etale direct image commutes with open restriction (its stated setting begins Let $A$ be a finite commutative ring and $p:V\to T$ a morphism of schemes [def-pc-scheme]. Let $i:W\); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-pc-derived-adjoint-functors: assumes ind/pro-system derived-functor existence and asserts a canonical adjunction; it does not identify the native fixed-pair model, its universal K-injective computation maps, or the concrete Hom-chain normalization.

lem-sf-native-weil-derived-hom-comparison vs lem-pd-section-derived-pushpull-normalization: the existing statement is about Section equivalence and canonical derived push-pull adjunctions (its stated setting begins Let $\Lambda$ be a commutative condensed ring [sk-def-sfb-condensed-ring], let $f:X\to Y$ be a morph); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-pur-derived-injective-boundary: the existing statement is about Normalized derived connecting maps from sequences exact on injectives (its stated setting begins Let C and A be abelian categories admitting chosen derived categories, with enough injectives in C. ); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-pur-injective-cone-boundary-descent: the existing statement is about Signed cone boundary and descent for functor rows exact on injectives (its stated setting begins Let $A$ be a commutative ring and $\mathcal C$ an abelian category with enough injectives [def-sp-ab); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-pur-module-supported-hom-transport: the existing statement is about Exact transport of module-valued normalized supported Hom (its stated setting begins Let A be a commutative ring, let (C,J) and (D,J') be sites with terminal objects and restriction arr); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-pur-support-pair-chain-coherence: the existing statement is about Adjoint chain maps on restriction kernels: maps and homotopies (its stated setting begins Let $\mathcal C,\mathcal D$ be small sites with abelian sheaf categories [def-weil-pbc-sites-and-coh); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-sbc-ambient-operations-scalar-linearity: the existing statement is about Scalar linearity of ordinary unbounded ringed pro-etale operations (its stated setting begins Let $A$ be a commutative ring, $u:U\to V$ a morphism of schemes with small pro-etale sites, and $R_U); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-sbc-unbounded-exact-adjunction-square: works on ordinary ringed-site modules and strict towers, and assumes the canonical unbounded derived adjunction; it does not construct or normalize the native Weil fixed-pair Hom chain.

lem-sf-native-weil-derived-hom-comparison vs lem-sc-p1-rhom-hom-derived-roof: the existing statement is about Natural RHom comparison with the cocycle roof formula (its stated setting begins Let $\mathcal A$ be an abelian category [def-sp-abelian] with enough injectives [def-sp-injective-re); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-sc-p1-rhom-hom-derived-roof-shift: the existing statement is about Unit-shift coherence of a roof-normalized natural RHom comparison (its stated setting begins Let $\mathcal A$ be an abelian category [def-sp-abelian] with enough injectives [def-sp-injective-re); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-sc-p1-rhom-hom-derived-roof-shift-injective-cocycle: the existing statement is about Shift coherence on a single cocycle in an injective representative (its stated setting begins Let C be an abelian category [def-sp-abelian] with enough injectives [def-sp-injective-resolutions],); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-sc-p1-rhom-injective-cocycle-bijective: the existing statement is about Bijectivity forced by the injective cocycle formula (its stated setting begins Under the abelian, enough-injectives, and derived-category assumptions [def-sp-abelian, def-sp-injec); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-sc-p1-rhom-natural-cocycle-map: the existing statement is about Natural additive RHom map normalized on injective cocycles (its stated setting begins Let $\mathcal A$ be abelian [def-sp-abelian] with enough injectives [def-sp-injective-resolutions], ); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-sf-exact-localization-derived-triangle: the existing statement is about Natural derived triangle of an exact localization sequence (its stated setting begins Let $C,D$ be abelian categories with derived categories. Let $F:C\to D$, $S:D\to C$ and $H:D\to D$ b); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-sf-fixed-pair-adjunction-lift: assumes abstract mate-compatible comparisons and proves only an underived fixed-pair adjunction; the model additionally specializes the actual native coefficient model and carries out its derived computation; the Hom node starts after that.

lem-sf-native-weil-derived-hom-comparison vs lem-sf-fixed-pair-derived-forget-comparison: concerns Grothendieckness and forgetting a derived lift; it does not provide this native inverse/direct-image pair or this Hom chain.

lem-sf-native-weil-derived-hom-comparison vs lem-sf-native-adic-pullback-frobenius-mates: supplies the underlying module comparison mate identity and exactness before lifting; it does not give the abelian Weil lift, its K-injective derived computation or normalized ambient Hom chain.

lem-sf-native-weil-derived-hom-comparison vs lem-sf-native-weil-constructible-abelian: covers Grothendieckness, exact conservative forgetting and constructible abelian closure; the new model adds the actual adjunction and its K-injective computation, and the Hom node concerns transposition, not abelian closure.

lem-sf-native-weil-derived-hom-comparison vs lem-sfb-cech-augmentation-normalized-naturality: the existing statement is about Counit normalization and resolution/refinement naturality of the Cech augmentation (its stated setting begins Let $\mathcal X,\mathcal Y$ be topoi presented by small sites in fixed larger coefficient universes ); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-sfb-cech-coefficient-derived-comparison: the existing statement is about Canonical coefficient comparison on the coherent Cech total (its stated setting begins Let $\mathcal X,\mathcal Y$ be topoi presented by small sites in fixed larger coefficient universes ); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-sfb-exact-postcomposition-kinjective-descent: the existing statement is about K-injective descent of comparisons after arbitrary exact functors (its stated setting begins Let $\mathcal A_0,\mathcal A_1,\mathcal B$ be abelian categories [def-sp-abelian] with ordinary unbo); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-sfb-galois-kinjective-section-model: the existing statement is about Exact singleton evaluation and K-injective Galois section model (its stated setting begins Let $k$ be a field, $k^s/k$ a separable closure [def-pd-separable-closure], $s=\operatorname{Spec}k$); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-sfb-integral-quotient-section-mate-realization: the existing statement is about Integral quotient scalar and geometric mate realization in section modules (its stated setting begins Fix a prime $\ell$, a finite extension $E/\mathbf Q_\ell$, its valuation ring $A=\mathcal O_E$, a un); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-sfb-kinjective-direct-image-open-word-model: the existing statement is about Simultaneous K-injective models and diagram descent for direct-image/open words (its stated setting begins Let $\Lambda$ be a commutative condensed ring [sk-def-sfb-condensed-ring]. On small representatives ); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-sfb-kinjective-hom-scalar-telescope: the existing statement is about Functorial K-injective Hom and scalar telescopes agree on every leg (its stated setting begins Let $\mathcal C$ be a site small in the module universe [def-weil-size-convention], let $R$ be a she); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-sfb-scalar-hom-telescope-evaluation: the existing statement is about Scalar localization internal-Hom comparison with every telescope leg and evaluation (its stated setting begins Let $\mathcal C$ be a site small in the module universe [def-weil-size-convention], $A$ a commutativ); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-sfb-topos-finite-free-counit-comparison: the existing statement is about Finite-free counit comparison on arbitrary sheaf topoi in specified coordinates (its stated setting begins Let $h:\mathscr X\to\mathscr Y$ be a morphism of sheaf topoi on sites small in the module universe [); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-sp-canonical-right-derived-adjunction-shift: proves canonical shift compatibility of an already available derived adjunction; it states neither the native model nor the detailed Hom-resolution comparison.

lem-sf-native-weil-derived-hom-comparison vs lem-sp-exact-pullback-derived-adjunction: has ordinary ringed-site module categories and K-flat source normalization; the native fixed-pair categories, their exact lifted pair, and the all-complex Hom chain with comparison-independence are not its statement.

lem-sf-native-weil-derived-hom-comparison vs lem-sp-levelwise-kinjective-tower-image: the existing statement is about Levelwise K-injective towers compute additive functors applied levelwise (its stated setting begins Let $\mathcal C,\mathcal D$ be sites small in the universe of [def-weil-size-convention], with sheav); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-trf-proetale-unit-leray-chain-formula: the existing statement is about Chain representative for ordinary pro-etale module cohomology pullback (its stated setting begins Let $h:X\to Y$ be a morphism of schemes [def-pc-scheme], and let $A$ be a finite commutative ring. U); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-weil-kinjective-total-derived-linear: the existing statement is about K-injective total right derived functors preserve scalar linearity (its stated setting begins Let $R$ be a commutative ring and $\mathcal A,\mathcal B$ abelian categories [def-sp-abelian] with $); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-weil-pbc-derived-exchange-bounded-comparison: the existing statement is about The bounded below exchange comparison equation (its stated setting begins Let (g':X'→X, f':X'→Y', f:X→Y, g:Y'→Y) be a cartesian square of schemes [def-weil-pbc-cartesian-squa); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-weil-pbc-derived-exchange-module-termwise: the existing statement is about K-injective representative of the module derived exchange mate (its stated setting begins Let $\Lambda$ be a commutative ring and let $f:X\to Y$, $f':X'\to Y'$, $g:Y'\to Y$, $g':X'\to X$ for); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-weil-pbc-derived-exchange-unbounded-transport: the existing statement is about Transport of the exchange equation to arbitrary K-injective representatives (its stated setting begins Let (g':X'→X, f':X'→Y', f:X→Y, g:Y'→Y) be a cartesian square of schemes [def-weil-pbc-cartesian-squa); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-weil-pbc-flat-restriction-derived-mate: the existing statement is about FlatRestrictionDerivedMate (its stated setting begins For a flat ringed diagram input x and small J [def-weil-pbc-flat-ringed-diagram-input], fix normaliz); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-weil-pbc-flat-scalar-tower-limit-square: the existing statement is about Flat scalar restriction and the normalized direct-image strict-limit square (its stated setting begins Let $u:\mathscr U\to\mathscr V$ be a geometric morphism of topoi presented by small sites, meaning $); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-weil-pbc-free-sheaf-derived-sections: the existing statement is about Free sheaf shifted Hom computes derived module global sections (its stated setting begins Let $Z$ be any scheme and $\Lambda$ any commutative ring. Let $\Lambda_Z$ be the sheafification of t); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-weil-pbc-kinjective-exact-square-comparison: the existing statement is about Normalized right-derived comparison for a K-injective-preserving exact square (its stated setting begins Let $\mathcal A',\mathcal A,\mathcal B',\mathcal B$ be abelian categories [def-sp-abelian], with unb); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-weil-pbc-kinjective-hom-derived: gives only localization Hom bijectivity into one K-injective target; the new statements construct the native model or compare its whole derived transposition.

lem-sf-native-weil-derived-hom-comparison vs lem-weil-pbc-kinjective-pullback-abutment: the existing statement is about K-injective representative of the unit--Leray abutment map (its stated setting begins Let $f:Y\to X$ be a scheme morphism, $K,L$ arbitrary complexes of abelian étale sheaves on $X,Y$ [de); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-weil-pbc-kinjective-unit-leray: the existing statement is about Unit--Leray computation on K-injective complexes (its stated setting begins Let $f:Y\to X$ be a scheme morphism [def-weil-pbc-scheme-conventions]. Let $I,J$ be K-injective coch); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-weil-pbc-qcqs-higher-direct-image: the existing statement is about Higher direct images for quasi-compact quasi-separated morphisms (its stated setting begins Let $u:U\to V$ be a quasi-compact and quasi-separated morphism [def-weil-pbc-scheme-conventions] of ); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-weil-pbc-right-adjoint-preserves-kinjective: gives only preservation for a supplied exact-left-adjoint pair; it supplies neither the native pair and its derived model nor the resolution-independent normalized Hom chain.

lem-sf-native-weil-derived-hom-comparison vs lem-weil-pbc-ring-sheaves-grothendieck: asserts Grothendieckness of ordinary module sheaves only; no native Frobenius adjunction, derived model or Hom normalization is included.

lem-sf-native-weil-derived-hom-comparison vs lem-weil-pbc-sequential-tower-evaluation-full: the existing statement is about Compatible derived evaluations lift to a strict derived tower map (its stated setting begins Let $\mathcal C$ be a small site and $R$ a sheaf of rings. Set $\mathcal A=\operatorname{Mod}(R)$ [d); it does not state the displayed native Weil Hom-transposition composite, independence in both representatives, and both normalized identity transposes.

lem-sf-native-weil-derived-hom-comparison vs lem-weil-pbc-termwise-adjunction-homotopy: states only the termwise/homotopy adjunction for a supplied additive adjunction; it neither constructs the native abelian adjunction and its K-injective model nor proves this specified derived Hom composite and normalization.

lem-sf-native-weil-injective-adjunction-model vs lem-sf-native-weil-derived-hom-comparison: the first constructs and computes the native underived pair without a derived Hom bijection; the second assumes that model and establishes the Hom comparison and its normalization, without constructing the pair or preserving constructibility.

## Original nine-step argument, retained verbatim

This is historical proof material for the two independent future workers. It is not proof steps assigned to the new unsplit nodes.

### Original step 1

For $T=X,Y$, use $B_T,\mathcal A_T,\mathcal W_T$ and the small-site/larger-universe convention of [def-sf-native-weil-derived-framework]. A $B_T$-module in sheaves of $\Omega$-vector spaces is equivalently a sheaf of $B_T$-modules: restriction of the $B_T$-action along $\underline\Omega\to B_T$ recovers its vector-space structure, and the two constructions preserve objects, maps and kernels. Thus [lem-weil-pbc-ring-sheaves-grothendieck] applies to $B_T$ and makes $\mathcal A_T$ Grothendieck abelian. By [lem-sf-native-adic-pullback-frobenius-mates], $P_T$ is an additive autoequivalence. Apply the first paragraph of [lem-sf-fixed-pair-derived-forget-comparison] to $\mathcal A_T$ and $P_T$. It makes the actual fixed-pair category $\mathcal W_T$ Grothendieck abelian and its forgetful functor exact and conservative. By [lem-sfb-grothendieck-k-injective], every complex in $\mathcal W_T$ has a K-injective resolution. All subsequent resolutions are in this abelian Weil category.

Uses: def-sf-native-weil-derived-framework, lem-weil-pbc-ring-sheaves-grothendieck, lem-sf-native-adic-pullback-frobenius-mates, lem-sf-fixed-pair-derived-forget-comparison, lem-sfb-grothendieck-k-injective.

Source: literature/stacks-project/injectives.tex; Tags 079Q (remark-existence-D) and 079P (theorem-K-injective-embedding-grothendieck); native fixed-pair specialization.

### Original step 2

Put $L=\bar f^*$ and $R=\bar f_*$ on the underlying module categories. Their canonical adjunction is [lem-weil-pbc-ringed-topoi-module-adjunction], for the coefficient map specified in the framework. By [lem-sf-native-adic-pullback-frobenius-mates], the actual comparisons $e:P_XL\cong LP_Y$ and $b:P_YR\cong RP_X$ obey the mate equation required in [lem-sf-fixed-pair-adjunction-lift]. Apply that lifting lemma with $\mathcal C=\mathcal A_Y$, $\mathcal D=\mathcal A_X$, $F=P_Y$ and $G=P_X$. It gives $F_0\dashv G_0$ on $\mathcal W_Y,\mathcal W_X$, where $F_0,G_0$ are precisely the framework's underived Weil inverse and direct images, with the ordinary unit $\eta$ and counit $\varepsilon$ as carrier maps. Both lifts are additive, since their underlying maps preserve sums. The lift $F_0$ is exact: forgetting a short exact sequence, applying the exact $L$, and using exactness and conservativity of the forgetful functor from step 1 proves this. Indeed the homology at each position has zero image under that functor, hence is zero.

Uses: def-sf-native-weil-derived-framework, lem-weil-pbc-ringed-topoi-module-adjunction, lem-sf-native-adic-pullback-frobenius-mates, lem-sf-fixed-pair-adjunction-lift, lem-sf-fixed-pair-derived-forget-comparison.

Source: lean/WeilConjectures/CategoryTheory/Endofunctor/IsoAlgebraAdjunction.lean; mapOfNatIsoAdjunction, lines 86–125; the exactness input is native adic Module.lean lines 170–178.

### Original step 3

Write $Q_T:K(\mathcal W_T)\to D(\mathcal W_T)$ for localization. By [lem-weil-pbc-termwise-adjunction-homotopy], the additive adjunction $F_0\dashv G_0$ of step 2 induces the termwise homotopy adjunction, whose Hom maps send $[u]$ to $[G_0u\circ\eta_M]$ and $[v]$ to $[\varepsilon_I\circ F_0v]$. Since $F_0$ is exact, [lem-weil-pbc-right-adjoint-preserves-kinjective] implies that $G_0I$ is K-injective whenever $I$ is K-injective. The framework defines $Rf_*$ as the total right derived functor $RG_0$ of [def-sfb-right-derived-functor], which exists since step 1 gives K-injective resolutions (the right-derived-functor clause of [sk-def-sfb-derived-categories]). Its unit $\eta^R:Q_YG_0\Rightarrow RG_0Q_X$ is natural in chain maps and invertible at every K-injective $I$, so $\eta^R_I:Q_Y(G_0I)\xrightarrow{\sim}Rf_*(Q_XI)$, and $RG_0(Q_XN)\cong Q_Y(G_0I)$ for $N\to I$ a K-injective resolution. This is the actual $Rf_*$ specified by the framework. The actual ambient $f^*$ is $D(F_0)$, the localization of the termwise exact inverse image.

Uses: lem-weil-pbc-termwise-adjunction-homotopy, lem-weil-pbc-right-adjoint-preserves-kinjective, sk-def-sfb-derived-categories, def-sfb-right-derived-functor, def-sf-native-weil-derived-framework.

Source: literature/stacks-project/derived.tex; Tag 08BJ (lemma-adjoint-preserve-K-injectives), including its homotopy Hom display.

### Original step 4

For arbitrary $T=Q_YM$ and $N=Q_XJ$ choose a K-injective resolution $r:J\to I$. Use step 3 and [lem-weil-pbc-kinjective-hom-derived] for both $I$ and $G_0I$ to form
$$\operatorname{Hom}_{D(\mathcal W_X)}(f^*T,N)\xrightarrow{Q_X(r)\circ-}\operatorname{Hom}_{D(\mathcal W_X)}(Q_XF_0M,Q_XI)\cong\operatorname{Hom}_{K(\mathcal W_X)}(F_0M,I)\cong\operatorname{Hom}_{K(\mathcal W_Y)}(M,G_0I)\cong\operatorname{Hom}_{D(\mathcal W_Y)}(T,Rf_*N).$$
The middle bijection is [lem-weil-pbc-termwise-adjunction-homotopy]. The first map is bijective because $r$ is a quasi-isomorphism, and the two outer localization Hom maps are bijective because their target complexes are K-injective. Denote the composite by $\Phi_{T,N}$. This is an ambient derived Hom bijection, including all extension morphisms of Weil sheaves.

Uses: lem-weil-pbc-kinjective-hom-derived, lem-weil-pbc-termwise-adjunction-homotopy.

Source: literature/stacks-project/derived.tex; Tag 070I (lemma-K-injective), (1) implies (3), and Tag 08BJ homotopy adjunction.

### Original step 5

The bijection $\Phi$ is natural in $T$. For a homotopy morphism $a:M'\to M$, the localization maps and the homotopy adjunction in [lem-weil-pbc-termwise-adjunction-homotopy] commute with precomposition by $a$ and $F_0a$. In the derived category every morphism is a composite of images of homotopy morphisms and inverses of localized quasi-isomorphisms, by the localization definition in [def-sf-native-weil-derived-framework]. An equality expressing naturality for an invertible arrow also expresses naturality for its inverse, by composing the equality on both sides with its inverse. Hence the same naturality holds for every derived morphism in $T$.

Uses: lem-weil-pbc-termwise-adjunction-homotopy, def-sf-native-weil-derived-framework.

Source: literature/stacks-project/derived.tex; Tags 070I and 08BJ; descent of the natural Hom comparison through localization.

### Original step 6

For naturality in $N$, choose K-injective representatives $I,I'$ of two derived objects. By [lem-weil-pbc-kinjective-hom-derived], a derived arrow between them has a unique homotopy-class representative $v:I\to I'$. Applying $G_0$ to $v$ is exactly the K-injective computation of $RG_0$ in [sk-def-sfb-derived-categories]: by naturality of the unit $\eta^R$ of [def-sfb-right-derived-functor] along $v$, $Rf_*(Q_Xv)\circ\eta^R_I=\eta^R_{I'}\circ Q_Y(G_0v)$ with $\eta^R_I,\eta^R_{I'}$ invertible, and the homotopy adjunction in [lem-weil-pbc-termwise-adjunction-homotopy] commutes with postcomposition by $v$ and $G_0v$. Thus the diagram for $\Phi$ commutes. The same Hom-computation lemma shows that two choices representing the same $N$ are connected by the unique homotopy-class map representing $\mathrm{id}_N$; that map is a homotopy equivalence. Applying the preceding naturality to it identifies the two constructions of $\Phi$. There is therefore no dependence on a representative or a resolution, and $\Phi$ is natural in both derived variables.

Uses: lem-weil-pbc-kinjective-hom-derived, sk-def-sfb-derived-categories, def-sfb-right-derived-functor, lem-weil-pbc-termwise-adjunction-homotopy.

Source: literature/stacks-project/derived.tex; Tag 070I (lemma-K-injective), uniqueness of representatives and quasi-isomorphisms between K-injectives.

### Original step 7

Define $\eta^d_T=\Phi_{T,f^*T}(\mathrm{id})$ and $\varepsilon^d_N=\Phi^{-1}_{Rf_*N,N}(\mathrm{id})$. The formulas of [lem-weil-pbc-termwise-adjunction-homotopy] identify these with the actual derived maps: if $T=Q_YM$ and $r:F_0M\to I$ is K-injective replacement, $\eta^d_T$ is represented by $M\xrightarrow{\eta_M}G_0F_0M\xrightarrow{G_0r}G_0I$. For $N=Q_XI$ with $I$ K-injective, $\varepsilon^d_N$ is $Q_X(\varepsilon_I):Q_XF_0G_0I\to Q_XI$, using the canonical computation isomorphism $\eta^R_I:Q_YG_0I\cong Rf_*N$ of [def-sfb-right-derived-functor]. Both follow by inserting identity maps into the middle Hom bijection of step 4. The independence proved in step 6 makes these formulas valid for the actual chosen derived functors.

Uses: lem-weil-pbc-termwise-adjunction-homotopy, def-sfb-right-derived-functor.

Source: literature/stacks-project/derived.tex; Tag 08BJ, homotopy Hom maps; derived unit and counit read from the constructed bijection.

### Original step 8

Naturality of $\Phi$ gives $\Phi(h)=Rf_*(h)\circ\eta^d_T$ and $\Phi^{-1}(a)=\varepsilon^d_N\circ f^*(a)$. Since $\Phi(\varepsilon^d_N)=\mathrm{id}$ and $\Phi^{-1}(\eta^d_T)=\mathrm{id}$ by definition, substitution gives
$$Rf_*(\varepsilon^d_N)\circ\eta^d_{Rf_*N}=\mathrm{id}_{Rf_*N},\qquad \varepsilon^d_{f^*T}\circ f^*(\eta^d_T)=\mathrm{id}_{f^*T}.$$
These are the two triangle identities. Thus the constructed natural Hom bijection defines an ambient adjunction $f^*\dashv Rf_*$, with exactly the derived unit and counit computed in step 7.

Uses: .

Source: literature/stacks-project/derived.tex; The exact-left-adjoint derived adjunction constructed using Tags 08BJ and 070I; formal triangle identities.

### Original step 9

Finally apply [lem-sf-native-weil-pullback-star-preservation] with the stated $f_0,X_0,Y_0$: its hypotheses are exactly the finite-field, separated finite-type hypotheses of this item. Hence $f^*T$ and $Rf_*N$ lie in the required bounded constructible subcategories whenever $T,N$ do. By [def-sf-native-weil-derived-framework] these are full subcategories, so both Hom sets in the item are precisely the ambient Hom sets in step 4. Restrict $\Phi$, its naturality, $\eta^d$ and $\varepsilon^d$ to these objects. Fullness retains every unit and counit component; their triangle equalities are the same equalities of ambient morphisms from step 8. This gives every clause of the stated adjunction on the actual restricted functors.

Uses: lem-sf-native-weil-pullback-star-preservation, def-sf-native-weil-derived-framework.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-lem-tensor-adjunction.proof.md; Step 1, last Hom bijection: restriction of the actual ambient derived adjunction.

## Validation

Server review_split passed. The first complete deliver.py --no-push exited 0 with OK (not pushed), preflight passed, at 3c66c8413f6. After that check I added an explicit definition dependency for Grothendieck abelian to the model statement and reduced the duplicate list to the source-tag pairs the delivery tool actually checks; no proof argument changed. The final bundle is dry-run again before pushing.
