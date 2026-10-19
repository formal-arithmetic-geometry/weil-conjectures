# Q21: lem-per-birational-bad-locus-comparison

1. Files written:
   - `dag/nodes/sec-deligne-laumon-a1/lem-per-birational-bad-locus-comparison.json`: statement, split into ten steps; no Mathlib match.
   - `dag/nodes/sec-deligne-laumon-a1/lem-per-proper-finite-coefficient-bounded-preservation.json`: one new statement-only unsplit lemma; no Mathlib match.
   - `citations.json`: a verbatim quotation of the statement used for each step/node pair.
2. Attachments: none. Searches of the read-only slopmaster2 project for the blueprint tag, birational comparison and bad-locus notions found no project declaration giving this result. The normalization and generic-irreducibility results are unrelated. The upstream master is reference material only.
3. WANTED: none. The ILO PDF and the Stacks tex sources needed here are available locally.
4. The imported item had no proof. Its statement has been retained, including the uniform induction hypothesis over variable schemes, the possibility of an empty bad locus, and its canonical comparison map. The proof follows ILO XIII 3.2.2, Proposition 3.4.2, and 3.5.1; it makes explicit the height inequality, the two cone calculations, and the spreading of the generic sections. It does not add finite Krull dimension or universal catenarity. No statement dispute was found. The generic-finiteness theorem is applied to proper dominant maps of integral schemes with a nonempty one-point generic fibre; its more general hypotheses are therefore met.
5. Work left: only the new proper-finiteness input remains unsplit at this one-level delivery. There is no unfinished step in the item. No Lean file was written, and no compiler, Lake or build tool was run.

The retained `searches.jsonl` was read rather than regenerated. It records the item's LeanFinder, Loogle, grep and LeanSearch queries, and all five searches recorded on the new node (including a second semantic phrasing). The hits are scheme-morphism properties, constructible subsets and general sheaf pushforward, not bounded constructible finite-coefficient etale direct image. The additional fibre-dimension searches are exploratory and did not create another node. The existing item's earlier search records were retained.

The whole-DAG and blueprint searches were checked again against the current repository. `blueprint_refs.py ancestor` gives `lem-per-artin-gabber-affine-curve`; `blueprint_refs.py search 0GL0` finds the finite-type-over-a-field compact-support result, which does not cover an arbitrary Noetherian base. Both item and new node have a precise ancestor place and `same_as: []`. This auxiliary proper-finiteness tool does not replace any unit or chapter step. The fixed unit and chapter files were read and left untouched.

## Review by Q21

I read the local ILO XIII text at 3.2.2 (formation and shrinking of the bad locus), 3.3 (the functorial comparison), Proposition 3.4.2 with both parts of its proof, and 3.5.1 (sections of the completely decomposed family), including its II 2.2.3 reference. This gives the same route as the item: take a codimension-c bad set upstairs, shrink it to finite disjoint components over T, spread rational lifts, and compare first with the full proper fibre and then with its bad closed subset. The ancestor is the finite-residue-duality step of the curve-perverse unit; all off-unit inputs are recorded as generic tools in `split_report.tool_uses` rather than a replacement route.

For the new node I read Stacks `more-etale.tex`, Tag 0GL0, `theorem-constructible-shriek`, whose conclusion is constructible cohomology for separated finitely presented qcqs morphisms and Noetherian torsion coefficients. For a proper map of Noetherian schemes its identity-open compactification is its ordinary direct image. I also read `etale-cohomology.tex`, Tag 095U, `lemma-cohomological-dimension-proper`: its bound is in terms of fibre dimension, not dimension of the base. To see that the new statement is valid without a globally finite-dimensional base, cover the base by finitely many affine opens and the finite-type source above each by finitely many affine finite-type charts. Each chart is a quotient of a polynomial algebra on finitely many generators. After taking a fibre its dimension is at most that number of generators; take their finite maximum n. Tag 095U gives vanishing above 2n for torsion abelian sheaves. For finite A the forgetful module comparison gives the same bound; finite cohomological truncations and 0GL0 give the asserted result for bounded complexes. This argument is recorded here, not hidden inside the new statement-only node. It needs no invertibility of the order of A. Finite maps (n=0), identity maps, zero complexes, empty schemes and coefficients of characteristic equal to the residue characteristic give no counterexample.

Step 1 uses the exact constant-ring inverse image in `prop-weil-pbc-inverse-image-modules-exact` and exactly the underlying-set pullback assertion of `lem-weil-pbc-constructible-etale-set-pullback`. Since B is finite, a finite B-module is the same finiteness condition as its underlying finite set. `thm-constructible-serre` supplies kernels, cokernels and extensions, so the long cohomology sequence proves triangle closure; it is not being cited merely as a definition. `lem-pc-right-derived-functor-triangulated` supplies the triangle-preserving derived functor. `lemma-weil-pbc-finite-direct-image-exact` and `lem-sbc-higher-direct-image-forget-comparison` together give closed module direct-image exactness. `lem-weil-pbc-open-closed-short-exact` explicitly includes modules and the adjunction maps. I added an explicit citation of `lem-weil-pbc-extension-by-zero-exact` already at this step so the passage to its complex triangle has all three exact functors justified.

Step 2 uses the no-finite-dimension version of `lem-per-quasi-excellent-finite-type-stability`: proper p is finite type, X' is quasi-compact, and every open or closed subscheme needed is again Noetherian quasi-excellent. Invertibility pulls back. Thus the induction hypothesis really applies to X' with the same c. `lem-weil-pbc-ringed-derived-slice-localization` states both derived localization and compatibility with units/counits, which is what later shrinking requires.

Step 3 uses the inequality, not the catenary equality, in `lem-trf-local-dimension-formula`. Here both schemes are integral, p is dominant locally finite type, and the generic function-field extension has transcendence degree zero because p is generically an isomorphism. Combining the inequality with height at least c upstairs and height at most c below forces s=t and residue transcendence degree zero. The strict-specialization height argument is the written prime-chain argument. Reduced components factor through reduced T by vanishing of its equations; set-theoretic inclusion alone has not been treated as sufficient for an arbitrary nonreduced scheme.

Step 4 uses `lem-weil-pbc-generic-finite-morphism-open-neighborhood` only for proper, finite-type, qcqs maps D→T with a nonempty finite generic fibre, a Noetherian target and an integral source. The proof writes the finite generic fibre argument: affine coordinate domains finitely generated inside an algebraic field are finite-dimensional fields. Properness then makes the images removed during shrinking closed. Distinct surviving generic fibre points make intersections miss t; their proper images may consequently be removed. This proves disjointness rather than assuming that distinct components were disjoint. The empty family is explicitly allowed.

Step 5 cites `lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods`, which supplies the small cofiltered affine-neighbourhood system, its affine transitions and its limit. `lem-sbc-pointed-section-stage-descent` states descent of an actual section over that system for a locally finitely presented target, rather than only descent of an object. The target here is etale. Complete decomposition supplies the residue-field-rational point at each generic point, and finiteness over T permits removing the image of the closed complement of its section domain. All these removed images miss t.

Step 6 uses the new proper-finiteness node for p_U, a proper map of the Noetherian schemes just checked. Both complexes in the unit triangle are therefore bounded constructible. Its cone vanishes on the dense isomorphism locus by the unit-compatible open localization from Step 2. The Step-1 open-closed triangle identifies this cone with a_*H, with H constructible by exact pullback.

Step 7 uses the same proper-finiteness input for the closed immersion of the reduced closure of Z. The induction hypothesis is applied on this possibly reducible Noetherian quasi-excellent closure with exactly the same integer c. Appending the generic point of integral X to a chain in the proper closed closure raises height by one. Thus the new exceptional closed set misses t and can be removed. `lem-cbc-etale-derived-direct-image-coherence` states the constant-module composition isomorphisms used to identify Rj_*a_*H with Rb_*Rv_*H, while Step 1 already gives underived closed direct image. If Z is empty, the cone is zero and the argument still applies.

Step 8 uses that same composition statement and `det-properbasechange-modules`. The latter explicitly asserts the specified constant-module exchange is an isomorphism for bounded-below complexes with torsion underlying cohomology. M is bounded below and B has characteristic ell, so every cohomology sheaf is killed by ell. The exchange is therefore applicable even though M is not yet known bounded constructible on the bad locus. I checked the arrow rather than only identifying its objects: twice transposing the unit gives the pulled-back counit, with the two adjunction triangle identities, so it is the requested base-change-unit comparison.

Step 9 uses `lem-weil-pbc-extension-by-zero-exact` to commute cohomology with open extension by zero. Adding the complementary zero stratum to the constructible stratification proves constructibility on the fibre. The new proper-finiteness node applies to q:F→T, a proper base change over a Noetherian closed subscheme. `lem-cbc-etale-derived-direct-image-coherence` identifies the target after the closed restriction, including the case T'=empty. Thus this second comparison also has bounded constructible cone.

Step 10 uses exactly the cone triangle for a composite written in the octahedral clause of `def-weil-triangulated-category`, and the Serre/long-exact-sequence closure already proved from `thm-constructible-serre` in Step 1. This is a short direct consequence of those statements, not another new lemma. The intersection of finitely many neighbourhoods still contains t. I checked the ten step lengths (each below 2000 characters); none hides a long standard lemma. I checked the zero complex, p an isomorphism, c=1, T contained in U, no surviving component, and coinciding images of distinct components. Nothing forces a nonempty T', and the second triangle handles its being empty.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the retained files: the sole new node is statement-only and self-contained; its sources use tags and labels; recorded searches have real successful log entries; blueprint and Lean attachment searches were made; every citation quote is copied verbatim from the current cited statement; generic tools are declared; neither cone calculation nor the entire item was moved into a new node. The separate `srvcheck` calls returned `check_dag OK` and `review_split PASS`. The final delivery dry run is still required after this report.

## Not duplicates

The new node packages proper bounded constructibility for arbitrary Noetherian schemes and finite constant rings. No global finite Krull dimension, fixed ground field, finite Tor amplitude, pro-etale transfer or adic tower is part of its hypotheses. In particular the stronger-looking finite-field ancestor cannot be used here: its proof descends through this item, which would create a cycle; the independent proper input is the one needed by ILO's two cone arguments.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-fd-finite-ring-compact-support-finiteness: Existing result assumes a finite-type target over a field; the new proper input allows an arbitrary Noetherian base.

lem-per-proper-finite-coefficient-bounded-preservation vs thm-fd-transform-well-defined: Existing result is well-definedness of the Fourier transform with finite-type-over-a-field target, not the general proper preservation tool.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-trf-oriented-proper-image-constructibility: Existing result is on oriented vanishing topoi with invertible coefficients, rather than ordinary small etale direct image.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-trf-global-operator-triangulated: Existing result is a morphism-of-triangles statement for cohomological correspondence operators over a field.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-trf-gabber-nearby-cycle-dimension-bound: Existing result bounds nearby cycles on a vanishing topos; it does not assert constructibility for proper direct image.

lem-per-proper-finite-coefficient-bounded-preservation vs sk-lem-proper-heart-bound: Existing result uses rational condensed coefficients and finite-type schemes over a field, with IndCons conclusions.

lem-per-proper-finite-coefficient-bounded-preservation vs det-ctf-finite-proper-tor: Existing result controls finite Tor amplitude in the standing finite-type-over-a-field setting.

lem-per-proper-finite-coefficient-bounded-preservation vs sk-lem-geo-finite-boundary: Existing result detects constructibility from a finite boundary and a given constructible pushforward; it does not supply proper preservation.

lem-per-proper-finite-coefficient-bounded-preservation vs sk-lem-geo-smooth-generic: Existing result is generic smooth direct-image lissity over a field, rather than proper preservation over arbitrary Noetherian schemes.

lem-per-proper-finite-coefficient-bounded-preservation vs det-proper-heart-bound-torsion: Existing result is cohomology of reductions of lisse lattices on weakly contractible pro-etale objects, over a field.

lem-per-proper-finite-coefficient-bounded-preservation vs det-prop-int-compactness-direct-sums: Existing result concerns integral condensed coefficients, localizing closures and direct sums over a field.

lem-per-proper-finite-coefficient-bounded-preservation vs det-ctf-finite-proper-localizing: Existing result concerns finite Tor amplitude and localizing categories over a field.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-per-quasi-excellent-etale-direct-image-finiteness: Existing ancestor treats finite fields and also nonproper maps over quasi-excellent bases; its proof depends on this item, so using it for the proper input is circular. The new proper-only statement is for any finite ring and has an independent Stacks source.

lem-per-proper-finite-coefficient-bounded-preservation vs def-weil-pbc-tower-preservation: Existing node defines preservation for adic towers; it is not a theorem proving finite-ring proper preservation.

lem-per-proper-finite-coefficient-bounded-preservation vs def-weil-pbc-local-acyclicity-abelian-sheaf: Existing node defines local acyclicity; it states no proper constructibility theorem.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-derived-adjunction-single-zero: Existing node is an abstract derived-adjunction comparison for complexes concentrated in one degree.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-exchange-strict-local-cohomology: Existing node identifies exchange on strict-local cohomology; it states no proper constructibility conclusion.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-etale-shriek-qcqs-composition: Existing node states composition of compact-support functors, not preservation of bounded constructibility.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-ind-etale-affine-strict-local-base-change: Existing node is ind-etale strict-local affine base change and does not state proper preservation.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-smooth-local-acyclicity: Existing node states smooth universal local acyclicity, not proper constructibility.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-etale-quasifinite-shriek-constructible: Existing node assumes a quasi-finite morphism and asserts constructible cohomology, not bounded constructibility for arbitrary proper maps.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-quasifinite-fp-finite-factorization: Existing node factors a quasi-finite morphism geometrically; it is not a direct-image finiteness statement.

lem-per-proper-finite-coefficient-bounded-preservation vs def-weil-pbc-proetale-modules: Existing node defines pro-etale modules and comparisons; it does not prove proper preservation.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-strict-local-geometric-fibre-test: Existing node tests strict-local geometric-fibre cohomology, not proper bounded constructibility.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-jointly-reflect-short-exact: Existing node is a categorical reflection criterion for short exactness.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-local-acyclicity-closed-fibre-unit: Existing node derives a closed-fibre unit comparison from local acyclicity, not proper preservation.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-strict-base-closed-point-localizations: Existing node compares strict-base closed-point localizations.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-etale-compact-support-base-change-qcqs: Existing node states compact-support base change, not constructibility or boundedness of that functor.

lem-per-proper-finite-coefficient-bounded-preservation vs thm-weil-pbc-amplification-proper: Existing node concerns pro-etale adic amplification over finite-dimensional Noetherian schemes with invertible torsion.

lem-per-proper-finite-coefficient-bounded-preservation vs prop-weil-pbc-preservation-constructible: Existing node preserves completed integral coefficients over finite-dimensional Noetherian schemes, not arbitrary finite rings on ordinary etale sites.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-etale-proper-direct-image-finiteness: Existing node assumes both schemes finite-dimensional and coefficient orders invertible; neither is available for the proper tool here.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-etale-open-cover-shriek-natural-ses: Existing node is the natural open-cover extension-by-zero short exact sequence.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-local-acyclicity-closed-fibre-unit-germ: Existing node compares closed-fibre unit germs under local acyclicity.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-quasifinite-affine-etale-thickening-decomposition: Existing node is a geometric quasi-finite affine etale-thickening decomposition.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-etale-open-cover-shriek-ses: Existing node is the open-cover extension-by-zero short exact sequence.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-etale-open-cover-shriek-complex-ses: Existing node is the open-cover termwise complex short exact sequence.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-etale-open-cover-shriek-triangle: Existing node is the open-cover extension-by-zero distinguished triangle.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-etale-affine-line-shriek-sheaf-constructible: Existing node treats constructible direct image with compact support along the affine line, not a general proper map.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-finite-fp-pushforward-constructible: Existing node assumes the map finite and states constructibility for sheaves; a general proper map is not finite.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-compatible-compactification-triangle: Existing node constructs a triangle for compatible compactifications, not general proper preservation.

lem-per-proper-finite-coefficient-bounded-preservation vs prop-weil-pbc-restriction-direct-image: Existing node assumes the FIN hypothesis and derives a pro-etale restriction; it does not supply FIN for a proper map.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-smooth-proper-specialization-prime-to-characteristic: Existing node states a smooth proper specialization isomorphism under invertibility.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-local-acyclicity-closed-fibre-ordinary-germ: Existing node compares ordinary closed-fibre germs under local acyclicity.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-constant-torsion-acyclic-devissage: Existing node is devissage from constant torsion acyclicity hypotheses.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-locally-constant-torsion-local-acyclicity: Existing node derives local acyclicity for locally constant torsion sheaves.

lem-per-proper-finite-coefficient-bounded-preservation vs prop-weil-pbc-amplification-consequences: Existing node derives adic consequences from amplification hypotheses, not this independent finite-ring finiteness input.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-strict-local-constant-comparison: Existing node compares constant strict-local cohomology.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-constructible-module-surjective-descent: Existing node is descent of constructibility along a surjection; it does not assert proper preservation.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-specialization-cospecialization-compatibility: Existing node asserts specialization/cospecialization compatibility under local acyclicity.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-proper-locally-acyclic-specialization: Existing node states specialization under proper local acyclicity, not bounded constructibility.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-etale-compactification-constructibility: Existing node supplies constructible cohomology for compactifications but does not supply any upper cohomological bound for a bounded input.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-etale-shriek-relative-mayer-vietoris: Existing node states relative Mayer-Vietoris for compact-support functors.

lem-per-proper-finite-coefficient-bounded-preservation vs def-weil-pbc-finite-level-amplification: Existing node defines finite-level amplification, rather than proving proper preservation.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-local-acyclicity-closed-fibre-stalks: Existing node computes closed-fibre stalk maps under local acyclicity.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-etale-shriek-compactification-independence: Existing node states compactification independence and cocycles, not constructibility or boundedness.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-finite-etale-pushforward-constructible: Existing node assumes finite etale maps and asserts sheaf constructibility.

lem-per-proper-finite-coefficient-bounded-preservation vs thm-weil-pbc-direct-image-finiteness-proper: Existing node assumes finite-dimensional schemes and invertible coefficient torsion, with pro-etale FIN bookkeeping; the new tool does not.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-pbc-local-acyclicity-strict-fibre-comparison: Existing node is a local-acyclicity strict-fibre comparison.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-pur-coprojection: Existing node is coprojection/purity for a closed immersion in the standing finite-type-over-a-field setting.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-etale-proper-derived-lower-star-coproducts-for-grothendieck: Existing node concerns arbitrary coproduct preservation of proper direct image, without a constructibility conclusion.

lem-per-proper-finite-coefficient-bounded-preservation vs det-sp-tower-bound-uniform: Existing node is a uniform bound for integral towers in the standing field setting.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-weil-structure-direct-images-constructible: Existing node is finiteness of structure-map ordinary/compact cohomology for schemes of finite type over the standing algebraically closed field.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-amb-unbounded-proper-open-interchange: Existing node interchanges proper direct image and open extension by zero; it does not assert bounded constructibility.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-sf-integral-compact-support-constructible: Existing node concerns integral compact-support images of derived-complete objects over a field.

lem-per-proper-finite-coefficient-bounded-preservation vs prop-trf-compact-support-perfectness: Existing node asserts perfect compact-support cohomology and stalks under finite Tor amplitude over the standing field.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-pur-projection-formula-coefficient-coherence: Existing node asserts projection-formula coefficient coherence in the standing field setting.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-kun-0f0c: Existing node states the unbounded proper base-change isomorphism, not constructibility.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-kun-proper-torsion-cd-bound: Existing node gives the torsion cohomological-dimension bound after a fibre-dimension bound is supplied, and does not assert constructibility.

lem-per-proper-finite-coefficient-bounded-preservation vs def-weil-integral-rational-qbar-compact-support: Existing node defines integral/rational/qbar compact-support functors over a field.

lem-per-proper-finite-coefficient-bounded-preservation vs thm-exc-direct-image-input-holds: Existing node supplies a direct-image input over a separably closed field with invertible coefficients; it does not cover arbitrary Noetherian bases.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-kun-relative-torsion-direct-image-dimension-bound: Existing node gives a vanishing bound over a separably closed field with a global source-dimension bound; it has no constructibility conclusion.

lem-per-proper-finite-coefficient-bounded-preservation vs prop-finite-compact-support-constructibility: Existing node assumes finite-type schemes over a field and special finite coefficient quotients, and includes coefficient comparisons.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-amb-proper-coproducts: Existing node states coproduct preservation for proper direct image, not bounded constructibility.

lem-per-proper-finite-coefficient-bounded-preservation vs lem-cbc-integral-compact-support-uniform-restriction: Existing node concerns completed integral compact-support functors on finite-dimensional schemes with ell invertible.
