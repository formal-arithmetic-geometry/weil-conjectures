# Stage 1 delivery: lem-sp-varying-ring-graph-summand

1. Files written: the unchanged-statement item, with a 1,920-character assembly proof, and the following three statement-only nodes (all unsplit, no Mathlib match):
   - dag/nodes/sec-smooth-purity/lem-sp-et-proet-graph-sheaf-square.json — statement; Adjunction-normalized site comparison of compactified graph sheaf maps; searched, not a Mathlib leaf.
   - dag/nodes/sec-smooth-purity/lem-sp-graph-derived-mate-factorization.json — statement; Derived mate factorization of compactified graph comparison; searched, not a Mathlib leaf.
   - dag/nodes/sec-smooth-purity/lem-sp-semilinear-compactified-graph-evaluation.json — statement; Compactified graph maps of semilinear systems and their evaluation; searched, not a Mathlib leaf.

2. Attachments: none. Searches of lean/WeilConjectures for the exact tag and graph/varying-ring notions found no complete exact declaration. The live Sheaf.Paper.VaryingRingGraphSummand module has relevant declarations with sorry, including varyingRingGraphSummand at line 686; it is not an attachment.
3. WANTED: none. The blueprint and the Stacks sources used are available locally.
4. The released 2026-10-22 repair order explicitly reopens the accepted 2026-10-17 split. Its defect is work granularity: eight steps total 8,468 characters. No mathematical error or change to the item statement is claimed. This repair distributes the arguments without changing the route or any maintainer-owned fields.
5. Unfinished: proofs of the three new nodes are deliberately left to their future workers, as required by the re-split order. Each new node has empty proof/proof_deps and proof_origin null. No Lean was written and nothing compiled.

## Review by Q106

I read the complete live item, its released repair note, the smooth-purity chapter and sk-prop-sp-tower-geometric unit, and the current det-sp-tower-gluing proof, especially Local pairs and Levels. I read Stacks etale-cohomology.tex, lemma-shriek-into-star-separated-etale (0F4L), more-etale.tex, lemma-separated-etale-shriek (0F4Y) and lemma-Rf-shriek-for-quasi-finite (0GKM), proetale.tex, lemma-jshriek-comparison (09AF), and derived.tex, lemma-pre-derived-adjoint-functors-general (0FND). The tower enhancement and the specified map comparisons are agent arguments, rather than claims that those tags state the whole item. No SGA route is used.

New node lem-sp-semilinear-compactified-graph-evaluation receives old steps 1–4. The graph is first open in the etale base change and then open in the compactification; it is closed as a section of the separated proper base change. Gluing on the graph/complement cover is meaningful even for pro-etale test objects. Linearity includes the constant-sheaf ring action; uniqueness on the two opens proves restriction and semilinear-transition compatibility. The general semilinear derived-sections node states operation/evaluation and mate compatibility for arbitrary strict inverse ring systems, not only an adic quotient system. I checked its statement and that of the exact localized-module extension adjunction. Evaluation is used on the constructed map, never to detect equality of arbitrary derived morphisms. The preserved argument below states each of these points.

New node lem-sp-et-proet-graph-sheaf-square receives old steps 5–6. I read the statements of weakly-etale localization, localized ringed-site morphism, exact site restriction adjunction, ordinary etale sum extension, classical module sheaves, open-extension site comparison, site-comparison morphism, pullback comparison and the definition of mate. In particular, localized direct image really is the identity on etale test objects with the same ring action. This gives the common right adjoint and therefore the specific adjunction-preserving sigma. Both transposed graph maps on a generator have eta(m) on the same graph and zero elsewhere; the open comparison restricts to the identity. Testing etale objects is valid after transposition, and only generator images before sheafification are claimed. I restricted the new site-square node to finite A, matching the explicit coefficient hypothesis of the cited open-comparison node.

New node lem-sp-graph-derived-mate-factorization receives old step 7 and the derived chain of step 8. I read the canonical Hom formula in lem-pc-pre-derived-adjoint-functors-general and the canonical-direct-image-mate statement. Substituting identity fractions and identity map makes the transpose of gamma the ordinary termwise counit. Underived mate normalization then identifies the two derived transposes, without inverting gamma or assuming comparison pullback preserves injectives. The graph-square substitution and naturality of gamma give the displayed two-equality derived chain. The new statement includes this chain so that the assembly does not hide the old argument. The generic existing lem-kun-derived-adjoint-square-comparison assumes an invertible underived direct-image comparison and an extra derived-functor hypothesis; our graph mate has neither assumption, so it is not a one-line instance of that node. General Mathlib derived counit formulas were read in Functor/Derived/Adjunction.lean (especially derivedε_fac_app, line 125); PointwiseRightDerived.lean line 80 characterizes a derived comparison but does not identify it with this specified counit mate. These are building blocks, not exact leaves for the full geometric statement.

Assembly step 1 cites exactly the first new statement, which states clopen graphs, their extensions, functoriality, the derived construction and its evaluation equation. I opened the delivered JSON and checked these clauses verbatim.

Assembly step 2 cites the second new statement for the specified sigma and its sheaf square, and the third for the actual derived factorization. It also cites def-weil-proper-morphism and lem-pur-site-restriction-module-adjunction-exact to check separatedness, quasi-compactness and exactness of j_!. The proper map is finite type and separated, hence qcqs; the input admits a bounded representative because it has bounded cohomology, and exact j_! preserves that bound. Each displayed arrow has source nu_T^*De_Sigma! L and target Rp_*j_!nu_U^*L after sigma. The new statements explicitly give those maps.

Assembly step 3 cites lem-weil-pbc-finite-type-over-noetherian: its statement gives Noetherian ascent from Spec k, which is Noetherian because a field has only the ideals 0 and k. I read lem-pur-etale-support-map-compatibility, whose statement explicitly says its inverse is the degreewise graph map followed by the derived comparison. I read lem-sp-et-proet-coefficient-compatibility, whose statement defines c^c as the counit-mate proper comparison followed by the open comparison. The hypotheses are all present: separated finite-type k-schemes, characteristic p>0, finite A annihilated by a power of ell distinct from p, bounded constructible finite-Tor etale input, and the chosen compactification. Thus the last substitution is the requested transported inverse, with the specified map rather than an unspecified isomorphism. These are generic tools already used by the accepted proof, not a replacement of the unit route.

I checked empty U, zero sheaf and zero ring (all maps have zero source), identity e with the identity compactification (the graph is the whole test object and the map is the ordinary comparison), and nonflat coefficient transitions such as Z/4 to Z/2 (the gluing argument uses only semilinearity and does not tensor). An arbitrary extra boundary component in the compactification does not invalidate clopenness: a section of its separated structure morphism is closed and it is open inside the open U-part. None of the new claims asserts arbitrary-input graph invertibility. The third node is deliberately bounded below, the domain on which the named proper site mate is specified.

I checked delivery-errors B–E against all four node files. Objects and coefficient categories are introduced in each new statement; no statement is a proof sketch. Sources name tags and labels; TeX uses single backslashes after JSON parsing. Existing-node/tag and whole-blueprint searches were performed before the files were created. No new node repeats the whole item: the first has the construction/evaluation task but no finite site normalization, the second is an underived site square, and the third is a bounded-below derived mate/factorization task. The human's explicit re-split order authorizes these three subarguments despite their supplying clauses of the assembly. Every old argument is retained verbatim below, with its complete uses and source, assigned to a future task. The only remaining finite-normalization substitution stays in the item. Proof dependencies equal the union of uses. citations.json contains a verbatim statement quote for every citation in every assembly step. The longest assembly step is under 1,000 characters. No chapter or unit record changes.

## Search evidence

searches.jsonl contains only results of the prescribed msearch.py commands. For each new node the JSON records its actual query strings and returned hit summaries: natural-language LeanSearch plus LeanFinder/Loogle and Mathlib grep, with alternative phrasings. Hits concern generic module sheafification, etale presentations, affine site equivalence, and derived adjunctions, rather than these geometric graph identities. Searches for the old item are retained unchanged. The whole blueprint was searched for graph, graph comparison, sum extension, counit mate, pre-derived, semilinear, and the combined graph/site/derived-square phrase. None states these three tasks. The item and each prospective task were also searched in WeilConjectures; no closed declaration states the item.

## Not duplicates

lem-sp-et-proet-graph-sheaf-square vs lem-coef-proper-identity-open-site-comparison: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Proper identity-open compact-support comparison is the inverse named mate. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-sf-compact-support-site-comparison-construction: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Canonical compact-support site comparison construction. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-coef-closed-identity-open-hom-normalization: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Identity-open normalization and domains of the closed exceptional Hom chain. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sf-compact-coefficient-composition: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Finite coefficient comparison respects compact-support composition. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sf-derived-immersion-comparison-normalization: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Derived open/closed site mates retain sheaf restriction normalization. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-trf-open-base-change-site-transport: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Site comparison preserves the named open base-change map. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-trf-compact-composition-tower-formula: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Computing finite pro-etale compact-support composition on a compatible tower. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-trf-finite-structural-maps-commshift: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Canonical finite-coefficient structural maps commute with shifts. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-trf-proper-composition-site-transport: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Site comparison preserves compact-support composition with a proper factor. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-trf-proper-open-site-transport: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Site comparison preserves finite proper/open interchange. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs sk-lem-uniform-constructible-ext: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Uniform Ext bound. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sf-etale-unit-tensor-arbitrary-base: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Canonical etale exceptional duality and its unit over arbitrary bases. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs det-ctf-finite-comparison-localizing: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns $\nu_X^*$ identifies the localizing closures. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sfb-quasifinite-compact-support-exact: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Quasi-finite compact support is exact and agrees with compactifications. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs det-proper-heart-bound-torsion: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns The torsion bound over a weakly contractible base. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sfb-etale-geometric-fibre-compact-sections: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Compact sections of a quasi-compact etale geometric fibre. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs det-uniform-constructible-ext-torsion: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns The torsion stratum bound. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-per-finite-etale-derived-ambidexterity: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Finite etale ambidexterity and its counit on ordinary derived categories. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-weil-pbc-etale-shriek-to-star-map: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns The canonical map from extension by zero to direct image for a finite etale morphism. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-weil-pbc-comparison-direct-image-canonical-mate: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Canonical derived direct-image comparison is the invertible counit mate. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-weil-pbc-etale-shriek-star-finite-modules: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Extension by zero equals direct image for finite etale module sheaves. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-weil-pbc-finite-etale-trace: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Restriction and trace of a finite etale morphism. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-weil-pbc-etale-graph-section-extension-map-linear: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns The presheaf map from the etale sum presheaf to direct image is linear over the constant sheaf of rings. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-weil-pbc-etale-graph-section-extension-map: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Sections over graphs extend by zero: the presheaf map from the etale sum presheaf to direct image. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-weil-pbc-etale-shriek-to-star-injective: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns The map from extension by zero to direct image is injective. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-weil-pbc-site-module-sheafification-lift-injective: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns A locally injective map into a sheaf induces an injective map on the sheafification. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-pur-finite-site-coordinates: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Finite Tate site comparison coordinates. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs prop-compactification-coherence-detailed: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Compactification coherence. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-asd-compact-support-graph-sheaf-normalization: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Graph comparison agrees with the canonical map into direct image. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-pur-projection-comparison-etale-origin: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Etale-origin comparison intertwines compact-support projection maps. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-fix-site-open-exchange: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Site comparison respects the normalized open base-change map. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-fix-site-open-exchange-sheaf: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Ordinary sheaf site comparison respects open exchange. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sp-open-scalar-site-coherence: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Open extension scalar/site square on flat models. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs thm-cbc-finite-level-proetale: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Finite-level pro-etale compact-support base change. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-amb-etale-adjoint-locality: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Etale localization of the ambient adjoint. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sf-open-comparison-tensor-normalization: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Tensor compatibility of the etale/pro-etale open-extension comparison. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-pur-finite-site-tensor-projection: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Finite-site tensor and projection coordinates. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-asd-compact-support-graph-geometric-base-change: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns The specified forward graph comparison at a geometric base change. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sp-et-proet-coefficient-compatibility: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Finite coefficient compact-support comparison respects site transport, refinement and composition. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sf-proper-open-comparison-site-normalization: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Normalization of the proper/open comparison under the site comparison. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-pur-proetale-affine-line-counit: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Restricted pro-etale affine-line counit. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sf-class-compact-support-comparison: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns On the coefficient class the compact-support functor is computed on the étale site. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-pur-supported-projective-site-arrows: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Supported Kummer projective-line arrows. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sp-varying-ring-graph-summand: this is a proper subargument of the reopened item, explicitly extracted by the human re-split order; the other two tasks and finite normalization are absent.

lem-sp-et-proet-graph-sheaf-square vs lem-sp-supported-etale-tensor-origin: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Bounded etale tensor origin for an open-supported finite-Tor complex. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-f7-etale-compactification-graph-map: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns The canonical etale compactification graph map. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-pur-vector-tensor-site-equations: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Canonical tensor integration comparison equations. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sp-tower-geometric-composition: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Geometric composition and exact etale sum-extension. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-pur-etale-horizontal-support-comparisons: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Canonical etale compact-support, horizontal composition and base-change comparisons. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sf-constructible-partition-local-closed-stratum: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Locally, a stratum of a constructible partition is closed with quasi-compact complement. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-cbc-finite-clopen-mate-site-transport: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Counit-normalized etale/pro-etale transport of the finite clopen mate. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-cbc-finite-constant-coefficient-transport: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Normalized finite scalar and etale-origin transport to constant coefficient modules. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-pur-supported-constant-exchange-normalization: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Canonical closed constant exchange and its underived comparison square. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs det-sp-reduction-exceptional: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Exceptional inverse image of a smooth morphism commutes with extension of coefficients. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-pur-finite-etale-dualizing-normalization: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Finite-coefficient etale exceptional normalization and its dualizing comparisons. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-asd-compact-support-finite-graph-isomorphism: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns The specified graph comparison for finite etale morphisms. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sp-proetale-proper-boundary-cohomology: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Boundary cohomology of an open-extended pro-etale injective on a proper scheme. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-pur-etale-horizontal-support-mate: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Etale horizontal compact-support exchange is the composition mate. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-pur-proetale-frame-integration: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Local pro-etale vector integration on a frame. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sp-etale-compactification-sheaf-scalar-map: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Ordinary compactified etale scalar mate on local sheet generators. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-pur-proetale-ordered-integration: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Ordered pro-etale affine integration. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-pur-open-site-comparison-arrows: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Derived open-extension and restriction site comparisons. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sp-finite-compact-site-coherence: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Finite-ring compact-support site comparisons respect refinements and towers. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sf-proetale-open-closed-sequence: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Open-closed short exact sequence on the pro-etale site. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-exc-etale-origin-open-restriction-transport: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Canonical comparison preserves normalized derived open restriction. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sp-supported-constructible-origin-comparison: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Supported constructible etale origin and its unbounded coefficient tensor comparison. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-pur-proetale-projection-integration: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Canonical proper integration counit. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-cbc-proetale-extension-zero-comparison: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Comparison of extension by zero with the site morphism. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-sp-constant-scalar-pullback-comparison: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Canonical constant-coefficient scalar extension, direct image and pullback comparison. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sp-open-proetale-counit-scalar: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns The actual pro-etale open counit under scalar extension. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-pur-proetale-vector-integration-arrows: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Canonical vector projection and integration arrows. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-pur-p1-kummer-trace-site-transport: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Supported Kummer projective-line decomposition, trace and open counit across sites. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-asd-compact-support-graph-comparison: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns The specified sheaf and unbounded derived graph comparison. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sp-etale-sum-coefficient-computation: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Sheetwise flat-complex computation of the compactified etale coefficient arrow. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-sp-fixed-compact-support-comparison: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Specified compact-support comparison on bounded-below etale representatives. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-asd-compact-support-graph-derived-isomorphism: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Invertibility of the specified graph map on unbounded complexes. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-pur-compact-support-graph-tensor-evaluation: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Tensor evaluation of the normalized compactification graph. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-sp-etale-compact-support-normalization: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Graph-normalized ordinary etale compact-support comparison datum. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-exc-etale-origin-proper-open-interchange: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Site transport preserves the canonical Cartesian proper/open interchange. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-weil-finite-compact-projection-formula: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Finite-coefficient compact-support projection formula. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-asd-etale-compact-support-normalization: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Normalization of compactified etale support and its exchange. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-amb-compact-support-open-factor: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns The open factor of compact-support site comparison. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-pur-proetale-projective-coefficient: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Projective tensor source comparison. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-cbc-strict-tower-proper-open-calculus: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Normalized proper/open calculus on strict pro-etale towers. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-amb-open-site-evaluation-counit: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Evaluation normalization for the open site comparison. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-sp-etale-adjoint-chart-comparison: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Derived sum adjunction and normalized etale chart left comparison. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-pur-vector-integration-site-comparison: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Finite-level site comparison of normalized vector-bundle integration. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-pur-etale-horizontal-support-tower: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Etale compact-support composition on a pullback compactification tower. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-pur-open-projection-site-transport: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Site transport of the normalized open tensor projection and its inverse. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-asd-compact-support-graph-sheaf-normalization-transpose: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Transpose of graph comparison. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-asd-compact-support-graph-coherence: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Base-change, proper-refinement and identity equations for the graph map. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-amb-compact-support-proper-factor: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns The proper factor of compact-support site comparison. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-pur-supported-projective-chern: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Supported projective-line Chern arrow. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sp-unbounded-open-counit-site-transport: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Unbounded degreewise open adjunctions and actual site-comparison counits. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-pur-etale-support-map-compatibility: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Etale proper-support normalization intertwines exchange and projection. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sp-finite-site-word-refinement: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Derived finite-site word comparisons and pushed proper-refinement pasting. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-pur-etale-sheaf-projection-map: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Etale sum-extension sheaf projection formula. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs thm-amb-vector-bundle-purity: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Vector-bundle purity before smooth orientation. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-amb-compact-support-site-comparison-open: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Bounded compactified site comparison commutes with open restriction. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-sf-open-comparison-unit-normalization: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Unit normalization of the etale/pro-etale open-extension comparison. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs def-pur-proetale-vector-integration: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Pro-etale vector integration and its adjoint arrows. Its statement does not identify both graph maps in this square.

lem-sp-et-proet-graph-sheaf-square vs lem-weil-pbc-proper-open-comparison-proetale: the new task is the explicit generator-normalized etale/pro-etale sheaf square for compactified graph maps; the existing node concerns Proper-open comparison for complexes from the etale site. Its statement does not identify both graph maps in this square.

lem-sp-graph-derived-mate-factorization vs lem-sbc-completed-operations-linear-natural-exchange: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Linearity and naturality of completed pullback, direct image, and exchange. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-sbc-unbounded-exact-adjunction-square: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Constant towers and evaluations preserve the unbounded derived adjunctions of a ringed morphism. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-coef-closed-adjunction-naturality: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Naturality of the evaluation-defined closed adjunction comparison. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-coef-derived-tower-counit-projections: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived constant/limit adjunction with its actual projection counit. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-coef-exact-sections-reduction-unit: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Exact sections identify principal derived reduction with the actual scalar-extension unit. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-coef-tower-coaugmentation: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Compact-support tower coaugmentation. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-coef-sequence-projection-derived-adjunction: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived adjunction of a ringed sequence projection. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-coef-monoidal-adjunction-parameter-composition: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Tensor-parameter composition under an adjunction with a tensor comparison. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-sf-derived-immersion-comparison-normalization: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived open/closed site mates retain sheaf restriction normalization. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-trf-integral-composition-counit-images: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Counit images of the two integral comparison composites. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-trf-continuous-cocontinuous-derived-shriek: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Unbounded derived lower shriek for continuous and cocontinuous site functors. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-trf-proetale-unit-leray-chain-formula: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Chain representative for ordinary pro-etale module cohomology pullback. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-trf-integral-inverse-image-comparison-composition: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns The integral inverse-image/pullback comparison respects composition. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-trf-point-reduction-unit-normalization: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Point coefficient-reduction comparisons are normalized by scalar-extension units. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-trf-graph-frobenius-point-exchange: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Ordinary Frobenius exchange followed by point transport is pullback. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-trf-integral-comparison-counit-characterization: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Whole-tower adjunct characterization of the specified integral comparison. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-trf-cotangent-flat-base-change: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived base change for ring cotangent complexes. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs def-trf-point-reduction-units: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Canonical scalar-extension units and exact restriction/sections identity at a point. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs def-trf-coefficient-tower-operations: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Coefficient tower operations and point sections. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pc-derived-adjunction-target-colimit: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Target Hom is the product colimit of transposed numerators. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pc-essentially-constant-pro-hom-colimit: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Hom out of an essentially constant pro-system value is the colimit of Hom sets. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pc-derived-adjoint-functors: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived functors of adjoint functors are adjoint. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs def-pc-derived-adjunction-hom-diagram: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Product diagram of fraction numerators. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pc-left-localization-hom-colimit: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Morphisms in a left localization are a colimit of ordinary Hom sets. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pc-colimit-fubini: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Fubini interchange for two categorical colimits. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pc-derived-adjunction-source-colimit: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Source Hom is the product colimit of numerators. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pc-pre-derived-adjoint-functors-general: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Pre-derived adjunction from essentially constant derived systems. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pc-essentially-constant-ind-hom-colimit: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Hom into an essentially constant ind-system value is the colimit of Hom sets. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pc-right-localization-hom-colimit: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Morphisms in a right localization are a colimit of ordinary Hom sets. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-sfb-divisible-extension-derived-reduction: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived reduction of an extension by a divisible sheaf. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-sfb-closed-test-derived-exchange-model: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived exchange on lifted closed pro-etale test objects. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-sfb-successive-derived-quotient-normalization: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Successive derived scalar extensions agree with direct quotient extension. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-sfb-scalar-adjunction-unit-coefficient-normalization: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Normalized scalar adjunction on K-flat models and the coefficient unit. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-sfb-adic-constructible-finite-reductions: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Finite reductions of a derived-complete constructible complex. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-sfb-derived-scalar-localization-reflection: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived scalar localization is reflective with its normalized unit. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-sfb-resolving-derived-adjunction-normalization: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived adjunction normalized by a left resolving class and K-injectives. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-sfb-derived-composition-adjunction-normalization: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived composition preserves the specified adjunction normalization. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-sfb-ringed-derived-monoidal-comparisons: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Monoidal and adjunction normalization of derived ringed-topos comparisons. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-weil-pbc-ringed-topoi-derived-pushforward-composition: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Canonical composition comparison for unbounded ringed-topos direct images. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-weil-pbc-strict-quotient-scalar-direct-isomorphisms: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Invertibility of the normalized ordinary and strict scalar right mates. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-weil-pbc-flat-restriction-derived-mate: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns FlatRestrictionDerivedMate. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-weil-pbc-termwise-adjunction-homotopy: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns An adjunction of additive functors induces an adjunction on the homotopy categories of complexes, termwise. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pbc-torsion-stalk-proetale-resolution-map: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Resolution-level pro-étale section map. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pbc-normalized-derived-adjunction-transport: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Transport of a normalized left derived adjunction through exact equivalences. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-weil-pbc-singleton-site-module-comparison: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Evaluation identifies the punctual ringed site with ordinary modules. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-weil-pbc-derived-exchange-module-termwise: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns K-injective representative of the module derived exchange mate. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-weil-pbc-strict-tower-exchange-mate-normalization: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Strict tower exchange agrees with the canonical mate. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-weil-pbc-ringed-derived-slice-localization: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived slice compatibility and pullback of section localizations. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs prop-weil-pbc-derived-inverse-image-adjunction: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived adjunction of inverse and direct image on D^+. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs def-weil-pbc-system-scalar-model: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Normalized ordinary and derived scalar model data. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs def-weil-pbc-flat-ringed-diagram-adjuncts: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Normalized coefficient comparison with adjunct compatibility. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs def-weil-pbc-flat-ringed-diagram-input: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Compatible flat coefficient input and its module diagram functors. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs def-weil-pbc-flat-ringed-diagram-comparisons: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Comparison functors and localization factors for flat coefficient restriction. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-weil-pbc-flat-ringed-diagram-restriction: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Flat coefficient restriction and normalized derived operations on module diagrams. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lemma-weil-pbc-projection-formula-totalization: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Signed totalization of the perfect formula. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs def-weil-pbc-system-scalar-coherence: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Canonical scalar restriction and derived tensor unit and composition maps. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lemma-weil-pbc-projection-formula-finite-free: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Finite-free projection formula. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-weil-pbc-flat-scalar-tower-exchange: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Flat scalar restriction transports the strict-diagram adjunction mate. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-system-derived-transition-coherence: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived semilinear transitions compose. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-extension-evaluation-comparison: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Evaluation comparison for derived left extensions. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-sheaf-ring-derived-coefficient-adjunction: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived change of rings along a map of ring sheaves is left adjoint to restriction of scalars, with normalized unit and transposes. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-sf-exact-pullback-counit-normalization: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Counit normalization of exact pullback and its strict completed construction. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-resolving-class-derived-adjunction: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Normalized derived adjunction from a resolving class. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-cochain-adjunction-compatibility: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Normalized derived Hom formulas on cochain complexes. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-cbc-cochain-augmentation-descent: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Descent of an augmentation through its universal cochain counit. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-system-derived-transition-unit: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Identity transitions and the canonical derived tensor unit. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-sp-varying-ring-graph-summand: this is a proper subargument of the reopened item, explicitly extracted by the human re-split order; the other two tasks and finite normalization are absent.

lem-sp-graph-derived-mate-factorization vs lem-sp-acyclic-flat-proper-coefficient-model: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Bounded acyclic flat models represent the proper coefficient map termwise. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-cbc-regular-quotient-cone-augmentation: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Normalized principal-quotient cone augmentation on K-flat sheaf complexes. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-sp-etale-derived-chain-transpose: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Canonical etale derived adjunction on ordinary chain transposes. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-comparison-direct-image-resolution-mate: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Restriction-transpose resolution model for the specified comparison mate. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-system-derived-subsequence-evaluation-composition: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Subsequence evaluation respects restriction composition. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-sf-completed-augmentation-adjunct: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns The specified completed augmentation is the normalized derived adjunct. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-sf-completed-pullback-mate-factorization: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Factorization of the actual completed-pullback comparison through the limit mate. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-system-selected-derived-composition: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Canonical composition of derived subsequence extensions. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-cochain-homotopy-derived-comparison: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Comparison through the homotopy quotient. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-ringed-coefficient-restriction-counit: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived ringed-topos counit under coefficient restriction. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-system-selected-derived-composition-evaluation: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Evaluation of the derived subsequence compositor. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-system-selected-derived-evaluation: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived evaluation of the subsequence left extension. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs def-sp-varying-ring-operations: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Canonical geometric operations on varying-ring systems. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-system-single-derived-evaluation: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived singleton evaluation below and above the input level. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-system-derived-subsequence-transition: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Subsequence evaluation respects derived transitions. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-exact-restriction-composition: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Exact restriction compositors and their localization formulas. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-system-level-left-extension: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived left extension from coefficient levels. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-derived-mate-comparison: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Cochain representative formula for normalized derived mates. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-system-derived-transition: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Localization of actual semilinear transitions. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-asd-derived-counit-k-injective-termwise: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Derived counit on a K-injective representative. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-normalized-adjunction-composition: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Composition and uniqueness of normalized adjunction formulas. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-sheaf-ring-derived-hom-comparison: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Compatibility of the derived scalar-extension adjunction with homotopy Hom representatives. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-adjunction-transition-coherence: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Transition coherence for evaluation mates. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-system-single-derived-extension: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Deriving the ordinary singleton extension. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-system-scalar-derived-extension: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns A scalar model as normalized derived extension data. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-system-selected-derived-extension: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Deriving the ordinary subsequence extension. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-adjunction-mate-transpose: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Transpose formula for a general mate square. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-adjunction-evaluation-composition: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Evaluation and composition of normalized adjunction mates. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-system-selected-derived-evaluation-index: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Reindexing the selected derived evaluation comparison. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-system-derived-subsequence: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Canonical exact derived subsequence comparisons. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-system-selected-derived-transition: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns The specified tensor-adjoint selected derived transition. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-cbc-cochain-derived-adjunction: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Normalized derived adjunction for a specified cochain left derived pair. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-pur-normalized-left-extension: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Normalized left extension from a resolving class. It does not provide this specific factorization under these hypotheses.

lem-sp-graph-derived-mate-factorization vs lem-kun-derived-adjoint-square-comparison: the new task identifies the actual bounded-below etale/pro-etale derived counit mate with the localized underived comparison and gives the resulting graph factorization; the existing node concerns Canonical right-derived comparison respects an exact adjoint square. It does not provide this specific factorization under these hypotheses.

lem-sp-semilinear-compactified-graph-evaluation vs lem-sf-etale-unit-tensor-arbitrary-base: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Canonical etale exceptional duality and its unit over arbitrary bases. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-sfb-quasifinite-compact-support-exact: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Quasi-finite compact support is exact and agrees with compactifications. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-sfb-etale-geometric-fibre-compact-sections: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Compact sections of a quasi-compact etale geometric fibre. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-per-finite-etale-derived-ambidexterity: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Finite etale ambidexterity and its counit on ordinary derived categories. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs def-weil-pbc-etale-shriek-to-star-map: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns The canonical map from extension by zero to direct image for a finite etale morphism. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-weil-pbc-etale-shriek-star-finite-modules: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Extension by zero equals direct image for finite etale module sheaves. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs def-weil-pbc-finite-etale-trace: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Restriction and trace of a finite etale morphism. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-weil-pbc-etale-graph-section-extension-map-linear: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns The presheaf map from the etale sum presheaf to direct image is linear over the constant sheaf of rings. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-weil-pbc-etale-graph-section-extension-map: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Sections over graphs extend by zero: the presheaf map from the etale sum presheaf to direct image. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-weil-pbc-etale-shriek-to-star-injective: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns The map from extension by zero to direct image is injective. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-weil-pbc-site-module-sheafification-lift-injective: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns A locally injective map into a sheaf induces an injective map on the sheafification. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-asd-compact-support-graph-sheaf-normalization: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Graph comparison agrees with the canonical map into direct image. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-amb-etale-adjoint-locality: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Etale localization of the ambient adjoint. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-asd-compact-support-graph-geometric-base-change: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns The specified forward graph comparison at a geometric base change. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-sp-et-proet-coefficient-compatibility: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Finite coefficient compact-support comparison respects site transport, refinement and composition. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-sp-varying-ring-graph-summand: this is a proper subargument of the reopened item, explicitly extracted by the human re-split order; the other two tasks and finite normalization are absent.

lem-sp-semilinear-compactified-graph-evaluation vs def-f7-etale-compactification-graph-map: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns The canonical etale compactification graph map. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-sp-tower-geometric-composition: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Geometric composition and exact etale sum-extension. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs def-pur-etale-horizontal-support-comparisons: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Canonical etale compact-support, horizontal composition and base-change comparisons. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs det-sp-reduction-exceptional: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Exceptional inverse image of a smooth morphism commutes with extension of coefficients. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-pur-finite-etale-dualizing-normalization: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Finite-coefficient etale exceptional normalization and its dualizing comparisons. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-asd-compact-support-finite-graph-isomorphism: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns The specified graph comparison for finite etale morphisms. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-pur-etale-horizontal-support-mate: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Etale horizontal compact-support exchange is the composition mate. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-sp-etale-compactification-sheaf-scalar-map: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Ordinary compactified etale scalar mate on local sheet generators. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs def-sp-constant-scalar-pullback-comparison: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Canonical constant-coefficient scalar extension, direct image and pullback comparison. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs def-asd-compact-support-graph-comparison: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns The specified sheaf and unbounded derived graph comparison. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-sp-etale-sum-coefficient-computation: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Sheetwise flat-complex computation of the compactified etale coefficient arrow. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs def-sp-fixed-compact-support-comparison: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Specified compact-support comparison on bounded-below etale representatives. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-asd-compact-support-graph-derived-isomorphism: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Invertibility of the specified graph map on unbounded complexes. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-pur-compact-support-graph-tensor-evaluation: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Tensor evaluation of the normalized compactification graph. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs def-sp-etale-compact-support-normalization: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Graph-normalized ordinary etale compact-support comparison datum. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-asd-etale-compact-support-normalization: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Normalization of compactified etale support and its exchange. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs def-sp-etale-adjoint-chart-comparison: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Derived sum adjunction and normalized etale chart left comparison. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-pur-etale-horizontal-support-tower: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Etale compact-support composition on a pullback compactification tower. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-asd-compact-support-graph-sheaf-normalization-transpose: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Transpose of graph comparison. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-asd-compact-support-graph-coherence: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Base-change, proper-refinement and identity equations for the graph map. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-pur-etale-support-map-compatibility: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Etale proper-support normalization intertwines exchange and projection. It does not give this system/evaluation assertion.

lem-sp-semilinear-compactified-graph-evaluation vs lem-pur-etale-sheaf-projection-map: the new task is the compactified pro-etale graph construction on arbitrary semilinear ring systems with the precise derived evaluation equation; the existing node concerns Etale sum-extension sheaf projection formula. It does not give this system/evaluation assertion.

## Preserved arguments for future workers

These are the old proof texts verbatim, not proof fields of the new nodes. Their uses are the existing interfaces the future split should audit. Ownership: old steps 1–4 belong to lem-sp-semilinear-compactified-graph-evaluation; 5–6 to lem-sp-et-proet-graph-sheaf-square; 7 and the displayed derived chain of 8 to lem-sp-graph-derived-mate-factorization. Step 8's Noetherian checks and final two normalizations stay in assembly step 3. The finite-clause hypotheses are unchanged.

### Old step 1

For a pro-etale test object V→T and a lift t:V→U, base change of the separated etale map e makes U×_T V→V separated etale. Its graph Γ_t is a section, hence an open and closed immersion by the etale-section lemma. The open immersion U×_T V→\overline U×_T V carries this graph to an open subscheme, while the same graph is closed in the latter product because it is a section of the separated base change of the proper morphism p. The graph therefore has an open-and-closed decomposition in the open part and a closed image in the compactification, exactly the geometry used for extension by zero. In particular the graph is clopen in the whole compactified product, since its open immersion is the composite of the graph open immersion with the base-changed open immersion.

Uses: def-pc-fibre-product, def-weil-etale-morphism, def-weil-proper-morphism, def-weil-open-immersion, lem-weil-pbc-etale-section-clopen-immersion, lem-weil-pbc-section-separated-closed-immersion, lem-weil-pbc-open-immersion-base-change, lem-weil-pbc-separated-base-change, lem-weil-pbc-etale-scheme-base-change

Source: {"document": "literature/stacks-project/etale-cohomology.tex", "place": "Tag 0F4L graph-section construction; Schemes Tag 01KT, section of a separated morphism; base-change stability; Morphisms Tag 02GO (lemma-base-change-etale)"}

### Old step 2

Put $\overline U_V=\overline U\times_TV$. Since Step 1 makes $\Gamma_t$ clopen in $\overline U_V$, use the disjoint open cover $\overline U_V=\Gamma_t\amalg(\overline U_V\setminus\Gamma_t)$ to glue $m\in M_n(V,t)$ and zero as sections of $j_!M_n$. On the graph, which lies in $U\times_TV$, open extension restricts to $M_n$; hence the gluing exists, is unique and is linear. Pullback of this cover along $V'\to V$ is the graph/complement cover for $t|_{V'}$, so uniqueness proves compatibility with restrictions. Finite sums of these maps define a presheaf-module map from [def-weil-extension-by-zero-presheaf] to $p_*j_!M_n$. Sheafification and [lem-pur-site-restriction-module-adjunction-exact] give the module-sheaf map. For a semilinear transition, both composites have the transitioned value on the same graph and zero on the complement; uniqueness proves the transition identity, without any flatness assumption on the ring maps.

Uses: def-weil-extension-by-zero-presheaf, def-weil-sheaf-of-modules-category, lem-pur-site-restriction-module-adjunction-exact, lem-coef-semilinear-derived-sections, def-pc-fibre-product

Source: {"document": "literature/stacks-project/etale-cohomology.tex", "place": "Tag 0F4L, first paragraph of the proof (graph sections and zero extension); Tag 03S5 fibre-sum presheaf formula"}

### Old step 3

The maps of Step 2 are natural in the coefficient sheaf because a module morphism commutes with restriction to the graph and to its complement. Apply the simultaneous section models for exact levelwise operations and their adjunction-mate comparisons from [lem-coef-semilinear-derived-sections]. The underived map sheafifies and then derives to a natural transformation θ:De_{Σ!,bullet}→Rp_{*,bullet}j_{!,bullet}. No inverse or isomorphism assertion is used in this construction.

Uses: lem-coef-semilinear-derived-sections, lem-pur-site-restriction-module-adjunction-exact

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gluing.proof.md", "place": "Local pairs paragraph: etale fibre sums and their tower-level derived operations"}

### Old step 4

The evaluation clause of [lem-coef-semilinear-derived-sections] applies to any strict inverse ring system, with no restriction to $\mathcal O_E/\ell^n$. Evaluation preserves the exact sum extension, open extension, derived direct image, the sheaf map of Step 2, and the specified adjunction comparisons used in Step 3. Thus evaluation of $\theta$ is precisely the analogous graph natural transformation $\theta_n:D(U_{\mathrm{proet}},R_n)\to D(T_{\mathrm{proet}},R_n)$ formed by the degreewise map followed by the derived direct-image comparison. No compact-support evaluation theorem for a special coefficient tower is needed.

Uses: lem-coef-semilinear-derived-sections

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gluing.proof.md", "place": "Levels: evaluation preserves the compact-support operations and their counits"}

### Old step 5

For the finite comparison fix a finite ring $A=R_n$. By [lem-weil-proetale-weakly-etale-localization], $U_{\mathrm{proet}}$ is the ringed slice $T_{\mathrm{proet}}/U$, with the same constant $A$-sheaf. Apply [lem-weil-pbc-localize-ringed-site-morphism] to the etale/pro-etale comparison and the object $U$. Its direct-image comparison is the identity on etale test objects, with the restricted ring action. Both $\nu_T^*e_{\Sigma!}^{\mathrm{et}}$ and $e_{\Sigma!}^{\mathrm{proet}}\nu_U^*$ are left adjoint to the resulting common right adjoint $\nu_{U,*}e_{\mathrm{proet}}^*=e_{\mathrm{et}}^*\nu_{T,*}$, using the exact slice sum-extension adjunction. The unique comparison preserving these adjunctions is
$$\sigma:\nu_T^*e_{\Sigma!}^{\mathrm{et}}\xrightarrow{\sim}e_{\Sigma!}^{\mathrm{proet}}\nu_U^*.$$
On an etale test object $W\to T$ it sends the image of a presheaf generator $(t,m)$ to the image of $(t,\eta_M(m))$: indeed the two adjunction units put $m$ in the same lift summand, and the localized direct-image identity changes neither $W$ nor $t$. This is an assertion about generators before sheafification, not an objectwise direct-sum formula for sheaf sections.

Uses: lem-weil-proetale-weakly-etale-localization, lem-weil-pbc-localize-ringed-site-morphism, lem-pur-site-restriction-module-adjunction-exact, def-weil-pbc-etale-sum-extension, def-weil-extension-by-zero-presheaf, lem-amb-etale-adjoint-locality

Source: {"document": "literature/stacks-project/proetale.tex", "place": "Tag 09AF (lemma-jshriek-comparison), adjunction proof; module refinement using the localized ringed-site identity"}

### Old step 6

Write $G^{\mathrm{et}}_M:e_{\Sigma!}^{\mathrm{et}}M\to p_*^{\mathrm{et}}j_!^{\mathrm{et}}M$ and $G^{\mathrm{proet}}_N$ for the graph sheaf maps, and $o_M:\nu_{\overline U}^*j_!^{\mathrm{et}}M\xrightarrow{\sim}j_!^{\mathrm{proet}}\nu_U^*M$ for the canonical open comparison. Let $d_{p,F}:\nu_T^*p_*^{\mathrm{et}}F\to p_*^{\mathrm{proet}}\nu_{\overline U}^*F$ be the underived counit mate of the inverse pullback comparison. Then
$$G^{\mathrm{proet}}_{\nu_U^*M}\sigma_M=p_*^{\mathrm{proet}}(o_M)d_{p,j_!^{\mathrm{et}}M}\nu_T^*(G^{\mathrm{et}}_M).$$
To check this equality, transpose under $\nu_T^*\dashv\nu_{T,*}$ and test a generator $(t,m)$ on an etale $W\to T$. The mate $d_p$ sends a section on $\overline U\times_TW$ to its comparison pullback: this is the underived counit formula, restriction to $W$, followed by the localization identity. The comparison pullback preserves restrictions, zero and the sheaf gluing. The open comparison $o$ is the identity after restriction to the open. Consequently both sides have value $\eta_M(m)$ on the same $\Gamma_t$ and zero on its complement. The classical module comparison identifies values of $\nu_U^*M$ on etale test objects with $M$ by its unit. Linearity and the sheafification universal property prove equality for every $M$. Testing here suffices because the maps have been transposed to maps of etale sheaves with source $e_{\Sigma!}^{\mathrm{et}}M$.

Uses: lem-cbc-proetale-extension-zero-comparison, def-weil-pbc-adjunction-mate, lem-weil-pbc-comparison-pullback, lem-weil-pbc-localize-ringed-site-morphism, det-pe-classical-sheaves-modules, def-weil-pbc-site-comparison-morphism, def-weil-pbc-etale-sum-extension

Source: {"document": "literature/stacks-project/etale-cohomology.tex", "place": "Tag 0F4L (lemma-shriek-into-star-separated-etale), graph calculation; proetale.tex Tag 09AF (lemma-jshriek-comparison); agent check of both transposed sheaf maps"}

### Old step 7

We check the derived comparison as a mate, rather than infer it from degree-zero agreement. For a bounded-below complex $P$ on $\overline U_{\mathrm{et}}$, write $Q$ for localization and
$$\gamma_P^{\mathrm{et}}:Q(p_*^{\mathrm{et}}P)\to Rp_*^{\mathrm{et}}QP,\qquad \gamma_{\nu^*P}^{\mathrm{proet}}:Q(p_*^{\mathrm{proet}}\nu^*P)\to Rp_*^{\mathrm{proet}}Q\nu^*P.$$
Let $a:\nu_{\overline U}^*p_{\mathrm{et}}^*\simeq p_{\mathrm{proet}}^*\nu_T^*$ and let $b_p$ be the specified derived counit mate of $a^{-1}$. The canonical Hom formula of [lem-pc-pre-derived-adjoint-functors-general], with $s=t=1$ and $f=1_{p_*P}$, says that the transpose of $\gamma_P$ is $Q(\varepsilon_P^0)$, the termwise underived counit. Thus the two maps
$$b_{p,QP}\nu_T^*(\gamma_P^{\mathrm{et}}),\qquad \gamma_{\nu^*P}^{\mathrm{proet}}Q(d_{p,P})$$
have transposes respectively $\nu_{\overline U}^*Q(\varepsilon_P^{0,\mathrm{et}})a^{-1}$ and $Q(\varepsilon_{\nu^*P}^{0,\mathrm{proet}}p_{\mathrm{proet}}^*(d_{p,P}))$. They are equal by the defining underived mate equation, degree by degree. The derived adjunction bijection gives
$$b_{p,QP}\nu_T^*(\gamma_P^{\mathrm{et}})=\gamma_{\nu^*P}^{\mathrm{proet}}Q(d_{p,P}).$$
Exact pullbacks and $a$ are applied termwise throughout. This computation uses no preservation of injective resolutions by $\nu^*$ and no invertibility of $\gamma$.

Uses: lem-pc-pre-derived-adjoint-functors-general, def-weil-pbc-adjunction-mate, lem-weil-pbc-comparison-pullback, lem-sf-comparison-pullback-exact, lem-weil-pbc-comparison-direct-image-canonical-mate

Source: {"document": "literature/stacks-project/derived.tex", "place": "Tag 0FND (lemma-pre-derived-adjoint-functors-general), canonical Hom formula; agent calculation with the underived and derived counit mates"}

### Old step 8

Now assume the finite clause of the item: $k$ is any field of characteristic $p>0$, $A$ is finite of $\ell$-power exponent with $\ell\ne p$, the schemes are separated finite type over $k$, and $L$ is bounded constructible finite-Tor. The schemes are Noetherian by [lem-weil-pbc-finite-type-over-noetherian] ($\operatorname{Spec}k$ is Noetherian since its only ideals are $0,k$), and $p$ is qcqs because it is proper. Choose a bounded representative $K$ of $L$ and put $P=j_!^{\mathrm{et}}K$ in Step 7. Apply $Q$ to Step 6 degreewise, then the pro-etale comparison $\gamma$. Naturality of $\gamma$ for $o_K$, followed by Step 7, gives explicitly
$$\begin{aligned}
\theta_n(\nu_U^*L)\sigma_L
&=\gamma^{\mathrm{proet}}Q(G^{\mathrm{proet}}_{\nu_U^*K})\sigma_K\\
&=Rp_*^{\mathrm{proet}}(o_K)\gamma^{\mathrm{proet}}_{\nu^*P}Q(d_{p,P})\nu_T^*Q(G^{\mathrm{et}}_K)\\
&=Rp_*^{\mathrm{proet}}(o_K)b_{p,QP}\nu_T^*(\gamma_P^{\mathrm{et}}Q(G^{\mathrm{et}}_K))\\
&=c_{e,A}^c(L)\nu_T^*((c_e^{c,\mathrm{et}}(L))^{-1}).
\end{aligned}$$
Here $c_e^{c,\mathrm{et}}$ is the sum-extension normalization of [lem-pur-etale-support-map-compatibility], whose inverse is exactly $\gamma^{\mathrm{et}}Q(G^{\mathrm{et}})$; $c_{e,A}^c=Rp_*^{\mathrm{proet}}(o)b_p$ is precisely the compact-support site comparison defined in [lem-sp-et-proet-coefficient-compatibility]. Thus the displayed equation proves the requested finite normalization with the specified $\sigma$, not just existence of an isomorphism. These are identities of the natural transformations on representatives, so [lem-weil-pbc-localization-universal-property] makes them equal as derived natural transformations; no finite-field hypothesis on $k$ or coefficient-change assertion is used.

Uses: lem-weil-pbc-finite-type-over-noetherian, def-weil-proper-morphism, lem-pur-etale-support-map-compatibility, lem-sp-et-proet-coefficient-compatibility, lem-weil-pbc-comparison-direct-image-canonical-mate, lem-sf-comparison-pullback-exact, lem-weil-pbc-localization-universal-property

Source: {"document": "literature/stacks-project/more-etale.tex", "place": "Tags 0F4Y (lemma-separated-etale-shriek), 0GKM (lemma-Rf-shriek-for-quasi-finite); agent assembly of the graph and mate equalities in Steps 6–7"}

## Validation

The first required server dry run exited 0 and printed OK (not pushed), commit 256d3f499e7. I then completed the first new node’s search records by adding the already-run LeanSearch query from searches.jsonl and named its constant-ring operation interface in stmt_deps. The final dry run checks this completed delivery before the push.
