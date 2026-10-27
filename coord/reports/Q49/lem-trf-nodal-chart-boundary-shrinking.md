1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-nodal-chart-boundary-shrinking.json`: split the assigned statement, unchanged, into four complete steps. No Mathlib match for the whole assertion.
- `dag/nodes/sec-trace-formula/lem-trf-nodal-polynomial-free-flat.json`: one new statement-only algebra/model lemma, unsplit. No Mathlib match; basis, flatness, and finite-presentation claims are independent of any boundary or etale chart.
- `citations.json`: one exact statement quotation for each step/dependency pair.

2. Attachments: none. Searched `lean/WeilConjectures/` for the blueprint tag, nodal charts, smooth nodes and boundary shrinking; no declaration states this item. The read-only `Sheaf/` material does not provide an attachment under the brief.

3. WANTED: none.

4. Defects found: the item itself is correct; no statement correction. Its original proof was empty. The key missing hypothesis when reusing the existing smooth-locus node is flatness of the model projection; this is supplied explicitly by the new helper. I did not infer flatness from smoothness of the chart away from T. The latest blueprint has replaced the ancestor's old nearby-duality proof by contracting correspondences; this is an assigned historical auxiliary branch and no unit or chapter route is changed by this split.

5. Unfinished: the new helper is intentionally statement-only for another stage-1 item. No part of the item's four-step assembly remains unstated.

## Proof idea for the new algebra helper (not part of its statement)

Over any ring A, reduction of a monomial u^i v^j replaces it by a^min(i,j) times the remaining pure power. Thus the pure powers and 1 span. For uniqueness, a polynomial supported on pure powers cannot be a nonzero multiple (uv-a)g: take the highest total-degree nonzero part g_d. The highest part of the product is uv g_d, nonzero because shifting monomials is injective even with zero divisors, and supported on mixed monomials. It cannot equal the highest part of a pure-power polynomial. Hence a reduced polynomial in the relation ideal is zero. This proves the basis over arbitrary A, including nilpotents and a=0. Tensoring with the direct sum of copies of A indexed by this basis is the direct sum of the input module; an injection remains coefficientwise injective, so B is flat from the tensor-injectivity definition. The affine flatness equivalence of Stacks 01U5 gives a flat scheme projection; the explicit two-generator one-relation presentation is finite, so 01TP gives local finite presentation. The assertions are local on the base and glue for W. This algebraic elaboration is by Q49, motivated by the model preceding curves.tex 0CBY; Stacks is not being claimed to state this exact basis lemma verbatim.

## Mathlib searches and reuse

All new searches were run through batch2/msearch.py, with original outputs retained in search-0.txt through search-6.txt and flat-search-0.txt through flat-search-5.txt; the exact query strings, actual results and verdicts are recorded in the JSON and searches.jsonl. Both natural-language phrasings were read. LeanFinder returned general smooth loci and standard smooth presentations, none stating this result. LeanSearch found Weierstrass nonsingularity and complements/zero loci for the item and generic flatness/presentation facts for the helper. Loogle returned no matches to the combined names. Source grep found interpolation uses of the word nodal, unrelated quotient bases, and no nodal model theorem. Polynomial.Monic.free_quotient was read in Mathlib/RingTheory/AdjoinRoot.lean (line 655); uv-a is not monic in v over A[u], so this is not a one-line specialization. General smooth-implies-flat cannot establish flatness at the nodal points.

Before adding the helper I searched the entire DAG for uv-h/xy-a/uv-a, nodal model, flatness, free/basis and the source tags, searched the project source for the same notions, and ran blueprint_refs.py ancestor on the item and search for nodal, xy, smooth locus, free basis and flat nodal. The existing lem-trf-nodal-model-etale-smooth-locus supplies the nonsmooth equivalence, so no new smooth-locus lemma is introduced. Its hypothesis is flat locally finite presentation and it does not assert the free basis or establish flatness. The other existing completion, local-model, and resolution nodes assume special bases or families and do not give the arbitrary-ring basis assertion.

## Review by Q49

I read ILO VI Proposition 1.9 on printed pages 70–71 (PDF pages 76–77), especially equation (1.a) and the assertion that h is invertible away from T. I followed curves.tex Tag 0CBY, lemma-etale-local-structure-nodal-family, and its preceding universal model, and checked morphisms.tex 01V9, lemma-smooth-at-point. The source's cited SGA reference is not used as a source: the proof route here uses ILO and Stacks. I also read the current blueprint ancestor and unit and the stored chapter/unit records. I checked all requirements B–E, including self-contained hypotheses, the meaning of each cited statement, elementary versus non-elementary steps, and the absence of relocated parent clauses.

For step 1 I read def-weil-closed-immersion, whose statement gives both the closed-subspace property and the affine quotient description, and lem-weil-pbc-etale-morphism-open-map, whose statement explicitly says the image of any etale map is open. The quotient by (u,v) is A/(h) without radicalizing h; restriction of constants and coordinates gives the same identification on overlaps. Thus the complement is closed in the actual closed subspace N, and its image is closed in V. The point t is in e(U), so it is not removed. No theorem about images of arbitrary closed subsets under an arbitrary morphism is used.

For step 2 I read lem-weil-pbc-open-fibre-product; its stated image formula and compatibility with projections identify restriction over an open with the inverse-image open. The chosen preimage r of a remaining node has p(r)=s in V circ and therefore lies in the restricted U. This argument establishes the requested coverage without asserting surjectivity onto all W or requiring residue-field-rational lifts. The step is elementary set reasoning from the cited open-base-change statement.

For step 3 I read the whole statement of lem-trf-nodal-model-etale-smooth-locus. It requires flatness and local finite presentation of f, both given for f=pi by the new helper. It allows arbitrary etale b and q; take b=id_V and q=e. The supplied e is the same V-morphism, and pi e=p is the structure-map equality. Its four-way equivalence then gives nonsmoothness of p at every lift of a node. This is precisely the sentence quoted in citations.json; I do not use its proof or its unrelated geometric-lift clause. Smoothness over the open V minus T means smoothness on a neighbourhood of any r over that open, so it contradicts this equivalence. I checked the hypotheses of the helper independently by the arbitrary-ring normal-form argument above. It is a smaller algebra lemma, neither the boundary-shrinking assertion nor a clause of the item.

For step 4 I checked the zero-locus meaning affine-locally: a is in no prime. The maximal-ideal argument gives ac=1, and uniqueness of inverses makes the local sections agree and hence glue by the structure-sheaf axiom. This is an elementary argument, not an uncited purity, descent, or normality theorem.

Small cases: h=0 forces the surviving open base into T, so invertibility is asserted only on the empty complement; if T=V the last assertion is likewise vacuous. A unit h would make N empty, incompatible with the given t, so no spurious pointed case arises. For A=k[epsilon]/(epsilon^2) and h=epsilon the identification N=Spec(A/(epsilon)) and closed-complement reasoning still apply. If e misses nodes over other base points, precisely those points form Z; we never delete p(t). Disconnected/non-quasi-compact schemes cause no difficulty since all arguments are pointwise or sheaf-local. The helper's normal-form basis also works for a zero divisor, a unit, a=0 and the zero ring. No Noetherian or reducedness assumption has slipped in. All four steps are shorter than 2000 characters. Dependency quotes were checked as literal substrings and the dependency union was checked when writing the files.

## Not duplicates

lem-trf-nodal-polynomial-free-flat vs def-sfb-nodal-branch-scheme: the existing node concerns the graph-exceptional-fibre construction of the relative nodal branch scheme; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs def-sfb-nodal-geometric-fibre-local-rings: the existing node concerns completed local ring, split-node ring and geometric-fibre projection; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-sfb-dvr-nodal-chart-blowup-calculus: the existing node concerns arithmetic nodal charts and their singular-point blowups; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-sfb-dvr-nodal-etale-local-form: the existing node concerns etale local equations of nodal curves over a dvr; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-sfb-log-pullback-nodal-image-integrality: the existing node concerns integral logarithmic pullback at nodal images, including persistent nodes; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-sfb-marked-nodal-relative-log-charts: the existing node concerns relative logarithmic charts for a marked nodal curve over a smooth pair; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-sfb-nodal-branch-double-cover: the existing node concerns the two branches of a nodal family form an etale double cover of its singular subscheme; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-sfb-nodal-graph-cone-base-change: the existing node concerns arbitrary base change and coherence of the nodal graph cone; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-sfb-nodal-graph-cone-chart: the existing node concerns the graded graph cone in an etale nodal chart; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-sfb-nodal-log-dualizing-pullback: the existing node concerns regular pullback of the logarithmic dualizing line along a nodal modification; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-sfb-nodal-section-dual-flat: the existing node concerns flat dual of the ideal of a section of a nodal family; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-sfb-nodal-trait-normalization-atlas: the existing node concerns etale atlas and finite descent for nodal trait normalization; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-sfb-nodal-trait-rational-domination: the existing node concerns rational geometric fibres dominate modifications of a nodal trait curve; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-sfb-persistent-node-normalization: the existing node concerns finite normalization at persistent nodes over an arbitrary trait; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-sfb-point-blowup-fibre-defects: the existing node concerns geometric fibre defects in regular surface point blowups; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-sfb-section-ideal-proj-expansion: the existing node concerns expansion from the dual ideal of an arbitrary section; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-sfb-smooth-generic-nodal-trait-normality: the existing node concerns normality and integrality of a smooth-generic nodal trait family; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-base-changed-algebra-differential-generators: the existing node concerns a chosen finite algebra generating family and its differentials after scalar extension; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-colimit-unramified-algebra: the existing node concerns unramified algebra maps descend along directed colimits; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-complete-intersection-fibres-limit-descent: the existing node concerns descent of flat families with local complete intersection geometric fibres; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-etale-descent-through-source-cover: the existing node concerns etaleness descends through a surjective etale source cover; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-exceptional-component-specialization: the existing node concerns an exceptional component has an exceptional component in each nonempty specialized closure fibre; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-finite-affine-limit-chart-family: the existing node concerns finite affine chart families with fixed presentations along an affine inverse limit; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-first-fitting-unramified-finite-stage: the existing node concerns base change and finite-stage unramifiedness of a first-fitting subscheme; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-formal-local-structure-nodal-family: the existing node concerns formal local equation at a split node; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-geometric-node-residue-rationalization: the existing node concerns rationalizing a geometric node over its finite separable residue field; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-lci-fibre-tensor-transition: the existing node concerns tensor transition and complete-intersection fibre comparison after scalar extension; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-lci-geometric-chart-descent: the existing node concerns descent of complete-intersection residue fibres on a chosen affine chart; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-lci-residue-chart-cover-extension: the existing node concerns residue-fibre complete-intersection charts cover after field extension; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-lci-unramified-singular-nodal-recognition: the existing node concerns nodal recognition from local complete intersection fibres and an unramified singular subscheme; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-nodal-chart-boundary-shrinking: the existing node concerns shrinking a nodal model chart to make its parameter invertible off a boundary; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-nodal-etale-chart: the existing node concerns etale normal forms for a nodal family with etale markings; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-nodal-family-etale-local-model: the existing node concerns etale local model uv=h of an at-worst-nodal family of relative dimension one; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-nodal-family-noetherian-approximation: the existing node concerns finite-type approximation of an affine nodal family; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-nodal-family-split-point-neighbourhood: the existing node concerns etale base neighbourhood making a prescribed nodal fibre point rational and split; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-nodal-generic-component-closure: the existing node concerns a smooth generic component in a nodal neighbourhood has a flat closure and finite etale boundary; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-nodal-limit-lci-pure-stage: the existing node concerns local-complete-intersection and pure-one-dimensional finite stages of a nodal limit; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-nodal-log-regularity: the existing node concerns log regularity of a marked nodal curve over a log regular pair; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-nodal-pair-projective-resolution: the existing node concerns resolution of a nodal curve over a smooth normal-crossings pair; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-nodal-point-finite-separable-splitting: the existing node concerns splitting a nodal curve point over a finite separable field extension; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-nodal-polynomial-model-completion: the existing node concerns completion of a polynomial nodal model at the origin; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-ordered-nodal-branch-overlap: the existing node concerns ordering nodal branches makes their vertical ideals agree generically on overlaps; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-outer-base-change-differential-comparison: the existing node concerns explicit differential comparison for simultaneous outer scalar extension; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-pointed-etale-diagram-pullback: the existing node concerns pullback of a pointed etale chart diagram through arbitrary base change and open restrictions; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-quadratic-completion-separable-splitting: the existing node concerns splitting a nondegenerate quadratic completed local algebra after degree at most two; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-rational-node-quadratic-completion: the existing node concerns quadratic completed equation at a rational geometric node; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-semistable-marked-base-change: the existing node concerns arbitrary base change of semistable marked curves and fibrewise stability; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-split-node-algebraization-finite-type: the existing node concerns algebraization of a rational split node over an affine integer finite-type base; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-syntomic-geometric-fibres-affine-criterion: the existing node concerns affine-local characterization of flat families with geometric complete-intersection fibres; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-syntomic-ring-filtered-colimit-descent: the existing node concerns descent of a syntomic algebra map along a directed colimit of base rings; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-valuation-smooth-branches-strict-chart: the existing node concerns smooth fibre branches give a zariski strict pair chart; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-valuation-symmetric-nodal-blowup: the existing node concerns symmetric blowup along the closure of one nodal point; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

lem-trf-nodal-polynomial-free-flat vs lem-trf-vertical-principal-ideal-fibre-detection: the existing node concerns fibre-generic detection of vertical principal ideals; the new lemma gives the pure-power module basis and flat locally finitely presented projection of uv-a over an arbitrary ring, without boundary, etale-chart, completeness, valuation, or curve-family hypotheses.

No new node is identified with a blueprint statement (`same_as: []`). The closed-complement topology and inverse-section gluing are proof steps rather than new nodes.

lem-trf-nodal-polynomial-free-flat vs lem-weil-pbc-qcqs-morphism-permanence: permanence of quasi-compactness and finite presentation does not establish flatness or a basis for the quotient uv-a.

lem-trf-nodal-polynomial-free-flat vs lem-sfb-noetherian-open-closed-finite-presentation: open/closed immersions over Noetherian schemes are different morphisms; the nodal model has arbitrary base and relative dimension one.

lem-trf-nodal-polynomial-free-flat vs lem-sfb-polynomial-quotient-proj-presentation: this is a proper projective homogeneous Proj construction over locally Noetherian bases, not the affine uv-a quotient or its free module basis.

lem-trf-nodal-polynomial-free-flat vs def-sbc-locally-finite-presentation: a definition of local finite presentation does not prove the pure-power basis or flatness.

lem-trf-nodal-polynomial-free-flat vs lem-trf-affine-chart-stalk-differentials: the existing node chooses finitely presented charts and identifies stalk differentials; it does not compute a basis or prove the nodal model flat.

lem-trf-nodal-polynomial-free-flat vs lem-trf-finite-locally-free-composition: composition of finite locally free maps does not apply to the infinite-rank free nodal algebra, which is not a finite morphism.

lem-trf-nodal-polynomial-free-flat vs lem-trf-structural-fibrewise-open-locality: locality of already-known structural properties does not establish flatness or the explicit pure-power basis of the nodal algebra.

lem-trf-nodal-polynomial-free-flat vs lem-nagata-polynomial-projection-flat: the existing node applies to a polynomial algebra, while uv-a is a quotient, not a polynomial algebra in general; flatness of a quotient does not follow from flatness of the polynomial ring.

lem-trf-nodal-polynomial-free-flat vs lem-weil-pbc-flat-morphism-affine-criterion: the affine criterion transfers a flat ring map to a flat morphism but does not prove that this quotient is a flat ring map or compute its basis.

lem-trf-nodal-polynomial-free-flat vs lem-weil-pbc-flat-ring-map-iff-flat-affine: affine flatness equivalence is a tool in the helper's future proof, not the explicit pure-power basis/flatness computation.

lem-trf-nodal-polynomial-free-flat vs lem-cbc-right-fibration-morphism-space: the existing node concerns mapping spaces in quasicategories and has no commutative-ring module-basis assertion; the tag collision is unrelated.

The first dry run requested these further tag-collision comparisons. I opened every listed node and read its statement before adding the comparisons; none states the new lemma or a generalization with a one-line specialization.
