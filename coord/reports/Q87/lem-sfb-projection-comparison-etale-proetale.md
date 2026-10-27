## Worker report

1. Files written: the unchanged-statement item dag/nodes/sec-six-functors-basics/lem-sfb-projection-comparison-etale-proetale.json (split); lem-sfb-etale-proetale-ringed-square-realization.json (new statement, unsplit, no Mathlib match); lem-sfb-constant-module-derived-projection-identification.json (new statement, unsplit, no Mathlib match); report.md and citations.json. Two new nodes, zero Mathlib leaves. The search command appended its actual results to searches.jsonl. The previous proof, report and searches were retained; prior-proof.json and prior-report.md preserve the previous attempt locally. No Lean or repository file was changed.
2. Attachments: none. The project-source search for the exact blueprint tag and projection/comparison names found no declaration under WeilConjectures stating the item. The recorded Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleProEtale theorem remains sorry, and the general rightAdjointProjectionMap_mate is only a categorical compatibility theorem requiring the geometric input data. ConstantSheafModule.lean proves statements about sections of constant sheaves, not either new derived realization statement.
3. WANTED: none.
4. This repairs the explicit re-split return. The earlier refusal to add nodes is superseded by the human's request to expose at least two separately claimable tasks. The parent's statement, target maps, finite discrete commutative coefficient hypothesis, qcqs hypothesis, and two D+ hypotheses are verbatim unchanged. The proof now has 1,853 characters. New nodes have self-contained statements, empty proof and proof_deps, status unsplit, sources, actual three-kind searches, and nearest-blueprint ancestry via this item. No statement dispute or source error was found.
5. The one-level split is complete. Proving the two new realization lemmas is deliberately future work for independent stage-1 workers. The earlier already-reviewed generic coherence and normalized comparison theorems are reused. No compiler, Lake, library build, or agent was started.

## Repair of every point of the return

The return requests at least two new statement-only nodes of comparable scope, rather than a shortened proof, and keeps the item statement fixed. This delivery adds exactly two: the concrete constant-ring square realization (1,828 statement characters) and the derived fixed-module/ringed-module map identification (about 2,700 statement characters). Neither states the parent's projection/exchange equality. The first has no direct-image exchange or projection formula at all. The second has one geometric morphism and compares two coefficient presentations, not an etale/pro-etale square or its projection/exchange identity. They can be worked on independently: neither new node depends on the other or on the parent.

The complete old work is retained and assigned explicitly. Old step 1's four constant-ring maps, their scalar and operation compatibility, the absence of a cartesian assumption, and the orientation theta=a^{-1} are the first new task. Old step 3's identification of the horizontal tensor maps and vertical projection maps with the specified fixed-coefficient constructions is the second new task. Its independently normalized K-flat and K-injective models also make precise the implicit change of coefficient presentation and D+-to-D adjunction compatibility in old step 2. Old step 2's equality of transposes and old step 3's target substitution are still written in the parent's steps 2 and 3, rather than discarded. Old step 4's restriction of naturality is still the parent's step 4, with the naturality of all realization maps included in the new statements. Thus this is a redistribution of the argument plus its explicit assembly, not deletion or paraphrase of the difficult compatibility.

The previous dry run was run first and allowed to exit. It confirmed the two old failures (3,239 proof characters; zero new nodes). That attempt pushed nothing. The new delivery corrects both and the stronger return's requirement of two nodes. The old report's no-new-node conclusion and its tool-conflict paragraph are historical only, preserved in prior-report.md; this report supersedes them.

## Sources and intended arguments for the new tasks

The chapter and unit records and their main-20261015 source files were read. The finite detail's clause (3), together with the parent unit's finite paragraph, requires transport of the canonical etale projection map, which is this item's precise role. The source is not a projection-isomorphism theorem for arbitrary unbounded factors. The current repository and retained item differ only in split_report and appended search records before this repair, so no newer proof or statement was overwritten.

For the first new task I read proetale.tex, section-morphism, the square immediately before Tag 09A6 (lemma-morphism-comparison). It supplies the geometric square for every scheme morphism; qcqs occurs only in the following pushforward assertion. Constant sheafification fixes the ring maps by constant sections. The ordinary module equivalence and the existing fixed-A comparison are named in the statement. The intended argument (here, not in its statement) is the full old operation argument: transport the zero, unit, addition, multiplication and each scalar map through the geometric comparison; naturality gives agreement on these operations. Both structural composites preserve constant sections, hence are the same sheafified ring map. The module maps consequently coincide with the specified module comparison. Exact localization gives the derived comparison, in inverse orientation theta=a^{-1}. This exposes the actual ringed input that generic square-coherence theorems assume.

For the second new task I read sites-modules.tex, lemma-adjoint-push-pull-modules, and Tag 03EL (lemma-tensor-product-pullback), and sites-cohomology.tex, Tags 07A4 (lemma-pullback-tensor-product) and 07A6 (lemma-adjoint). I also read the projection-map construction immediately preceding 0E48. The existing constant-module equivalence and lem-sfb-constant-scalar-geometric-adjunctions give the ordinary coefficient change and the actual ordinary adjunction comparison; they do not state its derived tensor or projection normalization. To prove the new task, compare balanced bilinear maps before sheafification; constant scalar restriction identifies the sheaf tensor and its pure-tensor map. The equivalence is exact and monoidal, so it preserves flatness, acyclicity and K-flatness. On flat-term K-flat complexes the signed direct-sum totalizations and the pullback tensor arrows are the same on every pure tensor, as in 07A4. On K-injective models, the ordinary normalized Hom bijections induce the derived ones of 07A6. Thus the units and counits agree, and their actual projection transposes agree. A bounded-below injective model also computes the unbounded direct image, fixing the inclusion compatibility. This is the hidden model-comparison work from old steps 2-3; it is not an assertion that an arbitrary equivalence preserves a chosen projection map without normalization.

The parent assembly uses Stacks 0E48 (remark-compatible-with-diagram) through the existing lem-weil-pbc-ringed-exchange-tensor-coherence, whose statement already contains the full generic identity and naturality. Its omitted verification is not silently assumed again. No SGA reference is used.

## Searches read

All pre-existing item searches were read from searches.jsonl and the earlier report and kept. No query was invented or repeated simply because of the previous failed transport/delivery.

For the first new node I ran LeanSearch on the constant-coefficient ringed square, LeanFinder on two phrasings (the derived tensor square and the scalar-preserving geometric comparison), Loogle on pullback/pushforward names, and grep for constant-ring/module equivalences and proetale comparison. One initial Loogle query had the nonexistent identifier CategoryTheory.SheafOfModules; this is recorded as an invalid query without an absence conclusion, and the corrected query uses SheafOfModules.pullback and SheafOfModules.pushforward. LeanFinder's first results concern formally etale algebras and Kaehler differentials, not topoi. The corrected Loogle results give ordinary SheafOfModules pullback composition and adjunctions. They neither construct this ringed square nor identify its fixed-A derived comparison.

For the second new node I ran LeanSearch, Loogle on SheafOfModules counits, grep, and two LeanFinder phrasings covering constant-module transport and K-flat/counit normalization. The ordinary pullback, pushforward, sheafification and scalar-adjunction results were read. In particular I opened Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean at the pullbackPushforwardAdjunction and PullbackConstruction.adjunction definitions, PushforwardContinuous.lean at pushforwardPushforwardAdj, and Presheaf/Sheafification.lean at toSheaf_map_sheafificationAdjunction_counit_app. These concern ordinary sheaves and do not assert agreement of fixed-coefficient derived K-flat tensor and K-injective adjunction models, their bounded-below inclusions, or their projection transposes. Therefore neither task is an exact Mathlib match or a one-line specialization. Every recorded query is in searches.jsonl with its actual result. No service was down.

Before creating either node I searched the whole DAG for 09A6, 07A4, 0E48, ringed comparison, constant-module equivalence, and adjunction restriction; searched the whole blueprint via tools/blueprint_refs.py search ('comparison tensor', 'exchange counit', 'mate restriction', 'ringed square', 'constant ring', 'projection mate'); and searched the project source by the parent's exact tag and by projection/comparison, constant-module, tensor and counit notions. The ancestry command gives det-thm-sfb-proper-base-change-finite. No equivalent imported blueprint statement was found; same_as is empty. The full same-source pair list follows, with the closest mathematical interfaces distinguished individually.

## Review by Q87

I reviewed the item and both new statements against delivery-errors B through E with the sources open. The new statements introduce all objects, categories, universes, constant-scalar normalizations and actual maps. They have no proof steps, proof sketch inside the statement, or proof dependencies. Their mathematical work is different from the parent's final identity, and the human's re-split instruction is met with two independent tasks rather than one child containing the whole theorem. The fixed-coefficient model identification is made explicit because an abstract endpoint isomorphism alone would not preserve the specified canonical map.

In parent step 1 I checked the statements of both new nodes. The first gives exactly the ringed square and theta=a^{-1}, not merely an untyped commutation of topoi. The second identifies the actual tensor comparisons and the adjoint-of-counit projection maps, for both vertical morphisms and horizontal comparison maps. Its hypothesis c is the constant-section ring isomorphism supplied for every edge by the first node. Both use the same small-site module universe. This addresses C4 for all geometric and canonical-map identifications in the step. The step is non-elementary because its substance is the two cited realization statements.

In step 2 I opened def-weil-pbc-adjunction-mate, lem-weil-pbc-comparison-direct-image-canonical-mate and lem-weil-pbc-ringed-exchange-tensor-coherence. The exchange theorem explicitly defines Ex as the mate of theta; the definition gives its transpose as the comparison followed by F_X of the etale counit. Substituting theta=a^{-1} gives exactly q_{p,B} of the normalized comparison statement, and the second new lemma says that these really are the same derived counits, including the bounded-below inclusion. The Hom bijection is injective, so the two named maps coincide. This remaining argument is elementary. The qcqs and finite-ring hypotheses are exactly those of the parent. Only B=K and B=L are used; neither N nor R_eK tensor N is assumed bounded below.

In step 3 I checked the entire displayed formula in the generic coherence statement, not only its concluding naturality sentence. Set f=p_et, f'=p_proet, g=nu_Y, g'=nu_X, E=K, Q=N. Its target identification is t_X followed by 1 tensor theta^{-1}; theta^{-1}=a, so it is precisely h, and after direct image it is R_p(h). Step 1 gives the actual tensor/projection maps; step 2 gives Ex_K=b_K and Ex_L=b_L. Substitution yields exactly both composites of the unchanged parent statement. No projection-isomorphism theorem is used. This step is non-elementary and cites the generic compatibility theorem.

In step 4 the coherence statement says natural in E,Q and the canonical-mate statement says natural on D+. The realization comparisons in the new nodes are natural as stated. A morphism between admissible pairs induces L to L' within D+, so the restrictions of those naturality squares make every replacement natural. Restriction and substitution are elementary; the naturality facts are explicitly cited. No properness, finite Tor, constructibility or invertibility hypothesis has appeared. Each step is below 2,000 characters. citations.json includes a verbatim excerpt for every use in every step (including the two full routes for step 3 and the exact transpose for step 2).

For C1/C3 I did not use the proof of an existing node as an interface. Generic tensor coherence, mate definition and normalized comparison are statement-level citations. The new nodes make precise the realization arguments formerly justified inline. Existing definition nodes are used to name the objects they actually define. The new nodes never depend on the parent, so no dependency cycle is introduced. Existing maintainer-owned tool_uses metadata is preserved; the active split_report tool uses retain only those still cited directly. lem-weil-pbc-ringed-exchange-tensor-coherence supplies generic square compatibility and lem-weil-pbc-comparison-direct-image-canonical-mate supplies the normalized named b, without replacing the unit route.

For E I tested the new statements at A=0, the empty site/topos and empty scheme, p=id and w=id, zero inputs, and A=Z/4. All scalar normalizations and ring-map equations are meaningful also for the zero ring. The empty ring sheaf has its unique structural isomorphism. The identity reduces both new identifications to their units. Tensor flatness is a sheaf property; the argument uses no stalks or assumption of enough points. Over Z/4 the assertion is a derived tensor statement and claims no finite Tor bound; unbounded N is allowed. Bounded-below inclusion is only used for K and L, not their tensor factors. The K-injective and K-flat models have compatible universes and exact equivalences preserve acyclicity. These checks found no false lemma, missing hypothesis or statement dispute. What changed is the required distribution of the realization work; the parent statement and route did not change.

## Not duplicates

lem-sfb-etale-proetale-ringed-square-realization vs def-fix-proper-etale-origin-scalar-data: the existing node concerns Canonical scalar, tensor and direct-image comparisons at etale origins; it does not assert the constant-section ring equation and actual fixed-A comparison for the etale/proetale site square.

lem-sfb-etale-proetale-ringed-square-realization vs det-proper-heart-bound-torsion: the existing node concerns The torsion bound over a weakly contractible base; it does not assert the constant-section ring equation and actual fixed-A comparison for the etale/proetale site square.

lem-sfb-etale-proetale-ringed-square-realization vs det-thm-sf-pf-adic-open: the existing node concerns Integral open direct image preserves constructibility; it does not assert the constant-section ring equation and actual fixed-A comparison for the etale/proetale site square.

lem-sfb-etale-proetale-ringed-square-realization vs det-uniform-constructible-ext-torsion: the existing node concerns The torsion stratum bound; it does not assert the constant-section ring equation and actual fixed-A comparison for the etale/proetale site square.

lem-sfb-etale-proetale-ringed-square-realization vs lem-amb-compact-support-site-comparison-open: the existing node concerns Bounded compactified site comparison commutes with open restriction; it does not assert the constant-section ring equation and actual fixed-A comparison for the etale/proetale site square.

lem-sfb-etale-proetale-ringed-square-realization vs lem-kun-inverse-image-monoidal: asserts invertibility of the etale fixed-coefficient tensor map; it does not compare coefficient presentations, all derived counits, or the ringed site square.

lem-sfb-etale-proetale-ringed-square-realization vs lem-kun-unbounded-exchange-agrees: compares etale base-change mates of a cartesian scheme square, including an abelian-coefficient assertion; it does not compare fixed-A and constant-ring module presentations.

lem-sfb-etale-proetale-ringed-square-realization vs lem-pd-module-ringed-topos-derived-comparison: compares internal modules for condensed coefficients on proetale sites of separated finite-type schemes; here the equivalence is from fixed discrete-A module-valued sheaves on arbitrary small sites, including etale and site-comparison morphisms.

lem-sfb-etale-proetale-ringed-square-realization vs lem-pd-section-derived-tensor-normalization: has internal-module and condensed pulled-back coefficient models; it does not compare fixed-A module-valued sheaves or their D+-to-D adjunctions.

lem-sfb-etale-proetale-ringed-square-realization vs lem-pe-direct-image-mate-compatibility: gives unit/counit equations for etale/proetale comparison on D+; it does not identify the full unbounded tensor and ringed-module models.

lem-sfb-etale-proetale-ringed-square-realization vs lem-pur-constant-native-pullback-monoidal: constructs a native monoidal structure with a flat-term normalization; it does not identify the independently specified ringed K-injective adjunction or bounded-below counit.

lem-sfb-etale-proetale-ringed-square-realization vs lem-sf-etale-origin-pushforward-amplitude: the existing node concerns Etale heart bounds control cohomological ranges on pro-etale complexes of etale origin; it does not assert the constant-section ring equation and actual fixed-A comparison for the etale/proetale site square.

lem-sfb-etale-proetale-ringed-square-realization vs lem-sf-finite-proetale-pushforward-constructible: the existing node concerns Intrinsic finite-coefficient constructibility under nonseparated finite-type pushforward; it does not assert the constant-section ring equation and actual fixed-A comparison for the etale/proetale site square.

lem-sfb-etale-proetale-ringed-square-realization vs lem-sfb-constant-scalar-geometric-adjunctions: gives the ordinary adjunction comparison; the new derived task additionally identifies flat/K-flat signed totals, the actual derived tensor and counit, projection transposes and D+ inclusions.

lem-sfb-etale-proetale-ringed-square-realization vs lem-sfb-finite-ctf-internal-etale-realization: the existing node concerns Finite internal-etale realization with Tor intervals and direct image; it does not assert the constant-section ring equation and actual fixed-A comparison for the etale/proetale site square.

lem-sfb-etale-proetale-ringed-square-realization vs lem-sfb-projection-comparison-etale-proetale: is the parent projection/exchange equality; the first new task has no projection/exchange map and the second has a single geometric morphism and compares coefficient presentations.

lem-sfb-etale-proetale-ringed-square-realization vs lem-sfb-ringed-comparison-tensor-adjunction: assumes a specified ring-compatible square and compares its two ringed paths; it does not construct the constant-A etale/proetale square or identify a fixed-module model.

lem-sfb-etale-proetale-ringed-square-realization vs lem-sfb-ringed-derived-monoidal-comparisons: compares composition/2-isomorphism constraints between already ringed module operations; it does not compare these operations with a fixed-A module-valued sheaf realization.

lem-sfb-etale-proetale-ringed-square-realization vs lem-sfb-ringed-derived-two-iso-comparison: assumes normalized ringed lifts and a ring-compatible 2-isomorphism; it does not establish those inputs for this site square or compare fixed-A sheaves with ring-sheaf modules.

lem-sfb-etale-proetale-ringed-square-realization vs lem-sp-finite-site-word-refinement: the existing node concerns Derived finite-site word comparisons and pushed proper-refinement pasting; it does not assert the constant-section ring equation and actual fixed-A comparison for the etale/proetale site square.

lem-sfb-etale-proetale-ringed-square-realization vs lem-weil-pbc-comparison-direct-image-canonical-mate: gives the normalized comparison mate and its invertibility; the first new task supplies its concrete ringed square input and the second compares fixed-A and ringed derived constructions.

lem-sfb-etale-proetale-ringed-square-realization vs lem-weil-pbc-ringed-exchange-tensor-coherence: assumes a ringed square and its canonical operations and proves a projection/exchange identity; neither new lemma states that identity.

lem-sfb-etale-proetale-ringed-square-realization vs lem-weil-pbc-ringed-projection-mate-exact: constructs and proves exactness for the ringed projection transformation; it does not identify that construction with fixed-A module-valued sheaf adjunctions.

lem-sfb-etale-proetale-ringed-square-realization vs lem-weil-pbc-ringed-square-tensor-compatibility: assumes a supplied ringed tensor-square presentation and flat-term normalization; it proves a representative tensor equation, not existence/identification of this constant-A realization.

lem-sfb-etale-proetale-ringed-square-realization vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: constructs a ringed pullback tensor isomorphism; it does not identify it with a separately constructed fixed-A module-valued sheaf model or construct the etale/proetale ringed square.

lem-sfb-etale-proetale-ringed-square-realization vs lem-weil-pbc-site-module-sheaf-constant-ring-equivalence: gives an equivalence and ordinary constant-module normalizations, not a geometric square or the derived tensor/adjunction/projection identifications.

lem-sfb-etale-proetale-ringed-square-realization vs sk-lem-proper-heart-bound: the existing node concerns A uniform bound for proper direct image; it does not assert the constant-section ring equation and actual fixed-A comparison for the etale/proetale site square.

lem-sfb-etale-proetale-ringed-square-realization vs sk-lem-uniform-constructible-ext: the existing node concerns Uniform Ext bound; it does not assert the constant-section ring equation and actual fixed-A comparison for the etale/proetale site square.

lem-sfb-etale-proetale-ringed-square-realization vs sk-thm-pe-direct-image-comparison: the existing node concerns Direct-image comparison; it does not assert the constant-section ring equation and actual fixed-A comparison for the etale/proetale site square.

lem-sfb-etale-proetale-ringed-square-realization vs stage3-proetale-comparison-counit: asserts the already normalized comparison counit equation; the new tasks construct the ringed-square realization and compare the underlying derived coefficient models.

lem-sfb-constant-module-derived-projection-identification vs def-asd-ordinary-supported-kummer-scalar: the existing node concerns Canonical derived scalar-change relation for supported Kummer classes; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-coef-compact-support-tensor-comparison: the existing node concerns Universal coefficient tensor presentations and canonical compact-support coefficient map; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-coef-ringed-sequence-site: the existing node concerns Canonical ringed sequence site for the coefficient quotient tower; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-coef-ringed-tensor-hom-model: the existing node concerns Canonical closed tensor-Hom representative model on a ringed site; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-coef-semilinear-derived-calculus: the existing node concerns Ordinary derived semilinear calculus interfaces; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-coef-semilinear-geometry-base: the existing node concerns Geometry base fields for coefficient linear operations; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-coef-semilinear-geometry-derived: the existing node concerns Derived geometric system operations and normalization; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-coef-semilinear-geometry-ops: the existing node concerns Canonical geometric mate and projection words; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-coef-semilinear-system-models: the existing node concerns Generic strict semilinear system constructions and representative normalization; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-fix-proper-etale-origin-scalar-data: the existing node concerns Canonical scalar, tensor and direct-image comparisons at etale origins; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-kun-commutative-exchange-raw-pullback: the existing node concerns Canonical transport of represented raw classes through a commutative square; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-kun-constant-projection-morphism: the existing node concerns Canonical constant-coefficient derived projection morphism; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pbc-successive-derived-scalar-normalization-data: the existing node concerns Normalized presentation data for successive derived scalar extensions; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pd-section-derived-realization: the existing node concerns Canonical derived section-module realization; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pd-section-derived-tensor-data: the existing node concerns Canonical derived section-module tensor data; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pur-adic-site-strict-quotient-interface: the existing node concerns Small-site adic strict quotient interface and canonical normalizations; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pur-cochain-coefficient-arrows: the existing node concerns Canonical scalar-association and transition arrows on cochain sheaves; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pur-cochain-coefficient-universe-transport: the existing node concerns Canonical common-universe transport of ring and module sheaves; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pur-cochain-tensor-coherence-data: the existing node concerns Canonical cochain ringed-pullback and coherence data; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pur-completed-pullback-tensor-comparison: the existing node concerns Canonical completed, rational and common-stage tensor pullback comparisons; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pur-etale-scalar-pullback-iso: the existing node concerns Canonical derived scalar and pullback isomorphism; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pur-finite-pullback-tensor-comparison: the existing node concerns Canonical finite derived pullback tensor comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pur-integral-line-reduction-data: the existing node concerns Signed integral line reduction and restriction data; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pur-open-coefficient-normalizations: the existing node concerns Exact-pullback and open-unit coefficient normalizations; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pur-ringed-coefficient-change-presentations: the existing node concerns Normalized coefficient changes between counit presentations; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pur-ringed-coefficient-counit-presentations: the existing node concerns Normalized ringed coefficient counit presentations; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pur-ringed-coefficient-projection-data: the existing node concerns Normalized coefficient projection interfaces; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pur-ringed-module-derived-operations: the existing node concerns Canonical module and derived operations for an exact ringed-site pullback; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pur-scalar-pullback-representative-data: the existing node concerns Canonical scalar/pullback representative data; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pur-sequence-adjoint-resolution-data: the existing node concerns Resolution data for the coefficient sequence projection; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-pur-system-tensor-mate-arrows: the existing node concerns Canonical tensor and proper/open arrows for varying coefficient systems; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-finite-coefficient-site-chain-tensor: the existing node concerns Canonical finite coefficient site comparison on total tensor complexes; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-finite-coefficient-site-hom-arrow: the existing node concerns Canonical finite coefficient site internal-Hom arrow; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-finite-coefficient-site-scalar-arrow: the existing node concerns Canonical finite coefficient site scalar comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-finite-open-tensor-operations: the existing node concerns Canonical finite open tensor and pullback operations; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-localized-strict-tensor-linear-evaluation-data: the existing node concerns Normalized coefficient-linear evaluation of localized strict tensor descent; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-open-normalization-data: the existing node concerns Geometric and operation data for open tensor normalization; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-point-evaluation-derived-compatibility: the existing node concerns Representative-normalized derived point comparisons; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-point-evaluation-scalar-coherence: the existing node concerns Tensor square for balanced point scalar data; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-point-evaluation-scalar-data: the existing node concerns Balanced scalar comparison for point sections; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-point-evaluation-tensor-coherence: the existing node concerns Signed tensor coherence for point sections; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-point-evaluation-tensor-data: the existing node concerns Normalized tensor presentation for point sections; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-point-fibre-tensor-common-stage: the existing node concerns Canonical common-stage point tensor and coefficient unit; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-point-fibre-tensor-finite-models: the existing node concerns Canonical finite point tensor normalization on K-flat representatives; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-point-fibre-tensor-models: the existing node concerns Canonical integral representative normalization; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-point-fibre-tensor-rational-compatibility: the existing node concerns Canonical rational point tensor, unit, and scalar compatibility; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-point-fibre-tensor-reduction: the existing node concerns Canonical module scalar tensor data and finite reduction squares; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-point-fibre-tensor-system: the existing node concerns Strong symmetric tensor comparison data for the point fibres; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-point-finite-source-constraints: the existing node concerns The finite point source uses the recorded tensor constraints; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-point-integral-scalar-square: the existing node concerns The integral point completion commutes with scalar extension; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sf-ringed-derived-adjoint-lift-data: the existing node concerns Data of a normalized derived adjoint lift of a ringed-topos morphism; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sfb-integral-quotient-coefficients: the existing node concerns Canonical integral uniformizer quotient coefficient maps; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sfb-integral-quotient-projection-map: the existing node concerns Integral quotient internal projection arrow; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sfb-internal-derived-scalar-comparisons: the existing node concerns Normalized internal derived scalar comparison interface; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sfb-internal-scalar-tensor-comparison: the existing node concerns Scalar-unit normalized tensor comparison for internal modules; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sfb-proetale-trace-coefficient-interfaces: the existing node concerns Canonical internal-module trace coefficient interfaces; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sfb-ringed-derived-comparison-data: the existing node concerns Data of normalized derived monoidal comparisons of ringed topoi; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sfb-ringed-projection-coherence-data: the existing node concerns Recorded data for tensor projection coherence; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sfb-ringed-slice-comparison-model: the existing node concerns Normalized ringed slice comparison data; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sfb-scalar-hom-canonical-iso: the existing node concerns Canonical internal-Hom comparison from a normalized scalar tensor map; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sfb-scalar-hom-comparison-data: the existing node concerns Actual scalar-adjunction and normalized tensor-Hom comparison data; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sp-constant-scalar-pullback-comparison: the existing node concerns Canonical constant-coefficient scalar extension, direct image and pullback comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sp-finite-free-direct-image-data: the existing node concerns Normalized scalar models and canonical coefficient comparison data; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sp-open-coefficient-adjunction-data: the existing node concerns Intrinsic open coefficient adjunction data; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sp-open-scalar-operations: the existing node concerns Constant-ring pro-etale scalar and open operations and their canonical comparisons; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sp-open-scalar-tensor-data: the existing node concerns Open scalar tensor normalization data; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sp-proetale-scalar-mate-identifications: the existing node concerns Normalized pro-etale scalar-to-tensor and coefficient-pullback identifications; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-sp-semilinear-constant-ring-operations: the existing node concerns Constant-ring semilinear system operations and normalized evaluation mates; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-trf-completion-unit-models: the existing node concerns Ordinary quotient adjunction and normalized derived completion models; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-trf-point-reduction-units: the existing node concerns Canonical scalar-extension units and exact restriction/sections identity at a point; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-trf-singleton-site-operations: the existing node concerns Punctual ringed-site operations and normalized comparison predicates; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-weil-pbc-derived-direct-image-composition: the existing node concerns Composition isomorphisms of derived direct images (conjugates of those of inverse images); it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-weil-pbc-derived-normalization-arrows: the existing node concerns Canonical derived coefficient normalization arrows; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-weil-pbc-normalized-origin-scalar-comparisons: the existing node concerns Canonical quotient scalar-extension unit and associator; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-weil-pbc-ringed-projection-restriction-data: the existing node concerns Normalized ringed projection and slice comparison data; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-weil-pbc-ringed-slice-derived-data: the existing node concerns Derived slice adjunction presentations and coherence squares; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-weil-pbc-ringed-tensor-square-presentation: the existing node concerns Representative presentation of a commutative ringed tensor square; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-weil-pbc-successive-derived-quotient-data: the existing node concerns Normalized presentations of derived coefficient extension; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs def-zl-ring-derived-scalar-extension: the existing node concerns Derived restriction and extension of scalars for ordinary modules; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-coef-enriched-sequence-projection-formula: the existing node concerns Uncurried finite projections of the enriched sequence adjunction; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-coef-etale-tensor-model-comparison: the existing node concerns Unique flat-model normalization of the étale scalar tensor comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-coef-exact-sections-reduction-unit: the existing node concerns Exact sections identify principal derived reduction with the actual scalar-extension unit; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-coef-ringed-pullback-hom-evaluation-comparison: the existing node concerns Evaluation-defined Hom comparison for ringed pullback; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-coef-scalar-hom-zero-compatibility: the existing node concerns Degree-zero normalization of scalar internal Hom; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-coef-semilinear-operations-existence: the existing node concerns Geometric and coefficient operations on a fixed semilinear system calculus; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-coef-semilinear-system-existence: the existing node concerns Ordinary semilinear system calculus and cartesian internal Hom; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-coef-sequence-projection-derived-adjunction: the existing node concerns Derived adjunction of a ringed sequence projection; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-coef-sequence-pushforward-limit-projections: the existing node concerns Restricted total-limit comparison with adjunction projections; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-derived-right-exact-tensor-comparison: the existing node concerns Normalized tensor comparison for a right exact strong monoidal functor; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-exc-proetale-constant-support-projection: the existing node concerns Constant-coefficient projection for compact support; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-exc-support-scalar-projection-normalization: the existing node concerns Normalization of support scalar mate as a projection arrow; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-fix-ringed-scalar-tensor-monoidal: the existing node concerns Normalized strong monoidality of derived scalar extension in independent universes; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-fix-tensor-pullback-square: the existing node concerns Tensor inverse-image comparisons commute around an open square; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-kun-adjunction-comparison-square: the existing node concerns Counit-compatible squares preserve the unique right-adjoint comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-kun-commutative-exchange-class-compatibility: the existing node concerns The exchange mate transports higher-image raw classes; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-kun-commutative-exchange-evaluation-compatibility: the existing node concerns Raw class evaluation commutes with geometric chart pullback; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-kun-derived-pullback-composition-monoidal: the existing node concerns Canonical derived etale inverse-image composition is monoidal; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-kun-derived-single-constants-comparison: the existing node concerns Exact constants comparison commutes with single complexes; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-kun-geometric-point-derived-sections-adjunction: the existing node concerns Derived geometric-point direct image is global sections with its adjunction; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-kun-geometric-point-projection-comparison: the existing node concerns Geometric-point projection morphism agrees with the constant-section projection morphism; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-kun-geometric-point-pullback-tensor-normalization: the existing node concerns Tensor normalization of the pullback/stalk evaluation comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-kun-inverse-image-monoidal: asserts invertibility of the etale fixed-coefficient tensor map; it does not compare coefficient presentations, all derived counits, or the ringed site square.

lem-sfb-constant-module-derived-projection-identification vs lem-kun-right-derived-single-counit: the existing node concerns Canonical derived counit on a single-object augmentation; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-kun-sections-adjunction-comparison: the existing node concerns Ordinary sections comparison from the constants adjunction; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-kun-single-adjunction-comparison: the existing node concerns Single-object comparison for composite derived adjunctions; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-kun-unbounded-exchange-agrees: compares etale base-change mates of a cartesian scheme square, including an abelian-coefficient assertion; it does not compare fixed-A and constant-ring module presentations.

lem-sfb-constant-module-derived-projection-identification vs lem-pbc-normalized-derived-adjunction-transport: the existing node concerns Transport of a normalized left derived adjunction through exact equivalences; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pd-module-ringed-topos-derived-comparison: compares internal modules for condensed coefficients on proetale sites of separated finite-type schemes; here the equivalence is from fixed discrete-A module-valued sheaves on arbitrary small sites, including etale and site-comparison morphisms.

lem-sfb-constant-module-derived-projection-identification vs lem-pd-section-derived-pushpull-normalization: the existing node concerns Section equivalence and canonical derived push-pull adjunctions; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pd-section-derived-tensor-normalization: has internal-module and condensed pulled-back coefficient models; it does not compare fixed-A module-valued sheaves or their D+-to-D adjunctions.

lem-sfb-constant-module-derived-projection-identification vs lem-pe-constructible-comparison-tensor-test-reflection: the existing node concerns Reflection of a single comparison tensor test; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pe-direct-image-mate-compatibility: gives unit/counit equations for etale/proetale comparison on D+; it does not identify the full unbounded tensor and ringed-module models.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-canonical-coefficient-system-geometry: the existing node concerns Geometric realization on the literal constant finite coefficient tower; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-cochain-comparison-monoidal-equations: the existing node concerns Monoidal equations for the canonical cochain pullback comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-cochain-pullback-tensor-coherence: the existing node concerns Signed tensor comparison and composition on cochain sheaf pullbacks; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-coefficient-associator-shifts: the existing node concerns Shift compatibility of balanced derived scalar associators; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-coefficient-pullback-shifts: the existing node concerns Shift compatibility of normalized inverse-image coefficient comparisons; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-common-stage-tensor-line-coherence: the existing node concerns Natural associativity and regular right unit for common-stage tensor; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-compact-support-completed-projection-coherence: the existing node concerns Completion coherence for the integral projection mate; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-constant-native-pullback-monoidal: constructs a native monoidal structure with a flat-term normalization; it does not identify the independently specified ringed K-injective adjunction or bounded-below counit.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-derived-pullback-tensor-iso: the existing node concerns Derived pullback commutes with derived tensor product on the constructible categories; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-etale-scalar-pullback-existence: the existing node concerns Existence of normalized derived scalar/pullback comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-etale-scalar-pullback-uniqueness: the existing node concerns Uniqueness of normalized derived scalar/pullback comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-exact-pullback-signed-comparison: the existing node concerns Exact ringed pullback identifies the canonical signed derived tensor comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-flat-term-kflat-tensor-native: the existing node concerns Total tensor of native flat-term K-flat complexes; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-geometric-scalar-association-cocycle: the existing node concerns Scalar-association cocycle from normalized inverse-image restriction squares; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-integral-ambient-operation-models: the existing node concerns Ambient completion presentations for integral pullback and tensor; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-integral-coherence-tower: the existing node concerns Coherence identities on normalized integral comparison towers; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-integral-line-derived-comparisons: the existing node concerns Normalized derived signed-line reductions and support; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-integral-line-power-comparisons: the existing node concerns Signed power scalar comparisons and evaluations; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-integral-line-reduction-restriction: the existing node concerns Signed line reductions and restriction to the derived-complete integral category; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-integral-line-restrictions: the existing node concerns Completeness and normalized restricted line equivalences; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-integral-tensor-reduction-tower-comparison: the existing node concerns Strict tensor comparison for finite coefficient-reduction towers; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-integral-tensor-transition-compatibility: the existing node concerns Quotient compatibility of the normalized total tensor comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-integral-tower-limit-comparison: the existing node concerns Derived limit of the strict integral comparison tower; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-kflat-total-tensor-model: the existing node concerns K-flat total tensor model for flat-term resolutions; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-module-tensor-coefficient-equations: the existing node concerns Ordinary module tensor equations for coefficient change; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-module-tensor-composition-equation: the existing node concerns Ordinary tensor square for composite module pullback; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-normalized-operation-system-models: the existing node concerns Normalization and simultaneous models for finite coefficient-system operations; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-normalized-tensor-constraint-transport: the existing node concerns Transport of normalized tensor constraints through coherent realization; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-ordinary-line-derived-scalar-comparison: the existing node concerns Ordinary unbounded derived scalar extension intertwines signed line tensor and evaluation; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-perfect-quotient-exchange-normalization: the existing node concerns Perfect quotient coefficient exchange with augmentation and completion-unit normalization; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-proetale-restricted-tensor-finite-local-constancy: the existing node concerns Finite local constancy of a restricted tensor with bounded-above inputs; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-ringed-coefficient-change-normalization: the existing node concerns Normalized coefficient changes and their naturality; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-ringed-coefficient-derived-presentation-exists: the existing node concerns Existence of a normalized derived coefficient presentation; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-ringed-coefficient-restriction-counit: the existing node concerns Derived ringed-topos counit under coefficient restriction; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-scalar-extension-tower-coherence: the existing node concerns Coherent quotient towers for integral scalar extension; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-scalar-hom-comparison-tower: the existing node concerns Evaluation-defined scalar Hom maps respect coefficient towers; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-scalar-tensor-pullback-normalization: the existing node concerns Scalar/tensor pullback normalization on a K-flat representative; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-scalar-tensor-unit: the existing node concerns Scalar action unitor for a normalized signed tensor comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-sheaf-ring-derived-coefficient-adjunction: the existing node concerns Derived change of rings along a map of ring sheaves is left adjoint to restriction of scalars, with normalized unit and transposes; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-sheaf-ring-derived-hom-comparison: the existing node concerns Compatibility of the derived scalar-extension adjunction with homotopy Hom representatives; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-signed-line-derived-base-change: the existing node concerns Signed line comparisons and their unbounded derived tensor action; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-strict-coefficient-comparison-calculus: the existing node concerns Simultaneous strict coefficient comparisons on ring-sheaf towers; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-support-site-comparison: the existing node concerns Etale-proetale comparison for supported sections and their exterior products; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-system-normalized-tensor-closure: the existing node concerns Normalized semilinear systems are closed under tensor and inverse image; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-system-tensor-reduction-formula: the existing node concerns Tensor formula for actual semilinear reduction adjoints; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-pur-varying-ring-tensor-comparison: the existing node concerns Normalized tensor comparison for one varying-ring inverse image; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sbc-derived-restriction-zero-transport: the existing node concerns Restriction triangle and coefficient transport in degree zero; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sbc-derived-section-pullback-zero: the existing node concerns Degree-zero derived section pullback before restriction coherence; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sbc-derived-section-single-unit: the existing node concerns Derived section pullback intertwines the two single-object units; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sbc-restricted-derived-evaluation-pullback: the existing node concerns The restricted derived section square for arbitrary source sheaves; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sbc-restricted-derived-section-shift-comparison: the existing node concerns Shifted single comparison for restricted derived section pullback; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sbc-restricted-derived-section-zero-comparison: the existing node concerns Zeroth comparison for restricted derived section pullback; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sbc-restricted-derived-sections-shift-transport: the existing node concerns Transport of restricted section pullback through the shift comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sbc-restricted-derived-sections-single: the existing node concerns Single comparison for restricted derived sections before homology; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sf-comparison-open-tensor-coherence: the existing node concerns Etale/pro-etale comparison respects the canonical open tensor map; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sf-completed-tensor-rational-naturality: the existing node concerns Naturality and rationalization of a completed tensor comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sf-generator-reduction-coherence: the existing node concerns Basic generator coefficient squares in semilinear systems; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sf-integral-line-tensor-comparison-representative: the existing node concerns K-flat line tensor models and finite balancing; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sf-open-operation-models: the existing node concerns Open operation comparisons with fixed tensor models and right square; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sf-open-restriction-completeness: the existing node concerns Completeness and the actual completion unit after ordinary open restriction; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sf-point-fibre-derived-tensor: the existing node concerns The point fibre functor preserves derived tensor at all coefficient stages; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sf-point-field-tensor-descent: the existing node concerns Rational and common-field point tensor descent; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sf-point-finite-tensor-comparisons: the existing node concerns Finite point tensor comparisons and all quotient squares; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sf-point-integral-completed-tensor-comparisons: the existing node concerns Completed integral point tensor and scalar squares; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sf-point-ringed-evaluation-model: the existing node concerns Ringed geometric-point evaluation with signed tensor and coefficient models; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sf-ringed-finite-free-tensor-complex: the existing node concerns Actual scalar tensor comparison on complexes and K-flat preservation; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-closed-scalar-hom-comparison: the existing node concerns Five Hom bijections and evaluation for a tensor-preserving left adjoint; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-closed-scalar-hom-composition: the existing node concerns Composition of the five closed-Hom bijections; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-closed-scalar-hom-transport: the existing node concerns Transport of closed-Hom comparison along adjoint isomorphisms; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-constant-scalar-geometric-adjunctions: gives the ordinary adjunction comparison; the new derived task additionally identifies flat/K-flat signed totals, the actual derived tensor and counit, projection transposes and D+ inclusions.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-derived-section-scalar-transport: the existing node concerns Localization transport of the normalized scalar adjunction; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-etale-stalk-total-tensor-comparison: the existing node concerns Canonical signed total tensor stalk comparison and chain naturality; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-exact-completed-koszul-pullback: the existing node concerns Exact product-preserving inverse image transports the actual Koszul unit; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-geometric-stalk-tensor-constant-single: the existing node concerns Geometric stalks commute with derived tensor against a constant module; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-hom-flat-scalar-evaluation-model: the existing node concerns Flat scalar evaluation on an arbitrary first complex and its derived coherence; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-integral-quotient-pullback-face-model: the existing node concerns Common K-flat model for integral quotient pullback faces; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-integral-quotient-section-mate-realization: the existing node concerns Integral quotient scalar and geometric mate realization in section modules; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-internal-extension-monoidal: the existing node concerns Scalar-unit normalized strong monoidal extension of internal scalars; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-internal-extension-preserves-flat: the existing node concerns Extension of scalars preserves flat internal modules; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-internal-scalar-mate-projection: the existing node concerns Restriction of an internal coefficient mate is the specified projection map; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-internal-scalar-mate-transitivity: the existing node concerns Successive internal coefficient mates and normalized scalar units; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-internal-scalar-pullback-normalization: the existing node concerns Normalized internal scalar extension and geometric pullback; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-projection-comparison-etale-proetale: is the parent projection/exchange equality; the first new task has no projection/exchange map and the second has a single geometric morphism and compares coefficient presentations.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-quotient-section-tensor-normalization: the existing node concerns Normalized quotient scalar tensors and section-module realization; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-resolving-derived-adjunction-normalization: the existing node concerns Derived adjunction normalized by a left resolving class and K-injectives; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-ringed-comparison-tensor-adjunction: assumes a specified ring-compatible square and compares its two ringed paths; it does not construct the constant-A etale/proetale square or identify a fixed-module model.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-ringed-derived-adjoint-lift: the existing node concerns Normalized ordinary and derived adjoint lifts of ringed-topos morphisms; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-ringed-derived-identity-comparison: the existing node concerns Identity comparison with normalized representative formulas; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-ringed-derived-monoidal-comparisons: compares composition/2-isomorphism constraints between already ringed module operations; it does not compare these operations with a fixed-A module-valued sheaf realization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-ringed-derived-tensor-diagrams: the existing node concerns Coherence equations for explicit canonical derived comparison maps; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-ringed-derived-tensor-lift: the existing node concerns Symmetric monoidal coherence of a canonical derived tensor lift; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-ringed-derived-two-iso-comparison: assumes normalized ringed lifts and a ring-compatible 2-isomorphism; it does not establish those inputs for this site square or compare fixed-A sheaves with ring-sheaf modules.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-ringed-projection-first-shift: the existing node concerns The ringed projection mate commutes with shifts in its direct-image input; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-ringed-projection-pullback-comparisons: the existing node concerns Normalized identity, composition and section pullback comparisons; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-ringed-projection-tensor-compatibility: the existing node concerns Tensor constraints and compatibility of normalized comparisons; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-ringed-projection-tensor-structure: the existing node concerns Canonical tensor structure in arbitrary recorded presentations; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-ringed-site-point-acyclic: the existing node concerns A conservative point family detects acyclicity; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-ringed-site-point-tensor: the existing node concerns Signed total tensor comparison for normalized stalks; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-scalar-hom-tensor-coherence: the existing node concerns Tensor coherence of the normalized scalar extension maps; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-scalar-internal-hom-tower-coherence: the existing node concerns Coefficient-tower and identity coherence for normalized internal Hom; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-scalar-tensor-comparison: the existing node concerns Derived scalar tensor comparison on all K-flat representatives; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sfb-scalar-tensor-tower-comparison: the existing node concerns Simultaneous normalized scalar tensor comparisons with coefficient coherence; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sp-bounded-flat-coefficient-site-square: the existing node concerns Bounded-flat coefficient/site square with its canonical derived comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sp-canonical-open-scalar-tensor-models: the existing node concerns Canonical scalar tensor models compatible with open inverse image; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sp-canonical-right-derived-adjunction-shift: the existing node concerns Canonical unbounded right-derived adjunctions commute with canonical shifts; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sp-etale-chart-comparison-isos: the existing node concerns Canonical site comparisons for scalar and chart operations; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sp-etale-derived-chain-transpose: the existing node concerns Canonical etale derived adjunction on ordinary chain transposes; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sp-exact-pullback-derived-adjunction: the existing node concerns Normalized derived adjunction of exact module pullback; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sp-finite-free-direct-image-shift: the existing node concerns Shift compatibility of the actual coefficient/direct-image mate; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sp-finite-free-scalar-models: the existing node concerns Existence of normalized actual-restriction scalar models; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sp-finite-free-scalar-shift: the existing node concerns The normalized scalar counit commutes with shifts and scalar extension is triangulated; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sp-intrinsic-open-projection-invertible: the existing node concerns Intrinsic open projection inverse is invertible; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sp-open-projection-scalar-comparison: the existing node concerns Scalar restriction of the normalized open projection; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sp-open-scalar-coefficient-coherence: the existing node concerns Coefficient coherence of scalar pullback; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sp-proetale-scalar-tensor-normalization: the existing node concerns Underlying tensor normalization of pro-etale scalar and inverse-image comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sp-proetale-tensor-coefficient-resolution-square: the existing node concerns Coefficient-resolution square for exact pro-etale tensor pullback; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sp-scalar-associator-conjugate: the existing node concerns Right conjugate of the normalized scalar associator; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sp-scalar-universal-derived-unit: the existing node concerns Canonical scalar universality in the exact-functor unit interface; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-sp-supported-constructible-origin-comparison: the existing node concerns Supported constructible etale origin and its unbounded coefficient tensor comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-trf-completion-unit-canonical-models: the existing node concerns Compatible ordinary and derived presentations of the coefficient adjunction; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-trf-point-reduction-unit-normalization: the existing node concerns Point coefficient-reduction comparisons are normalized by scalar-extension units; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-trf-proetale-unit-leray-chain-formula: the existing node concerns Chain representative for ordinary pro-etale module cohomology pullback; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-derived-scalar-extension-restriction-adjunction: the existing node concerns Derived reduction modulo varpi^n is left adjoint to restriction of scalars; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-etale-native-tensor-pullback: the existing node concerns Native unbounded derived tensor commutes with etale inverse image; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-augmented-cech-tensor-pullback: the existing node concerns Augmented Cech tensor actions commute with derived inverse image; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-augmented-diagram-projection-mate: the existing node concerns Projection mate for an augmented coefficient diagram before taking inverse limit; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-cochain-pullback-tensor-shift: the existing node concerns The prescribed cochain pullback tensor comparison commutes with both signed shifts; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-cohomology-pullback-derived-unit: the existing node concerns The cohomology pullback is induced by the unit of the derived adjunction; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-comparison-direct-image-canonical-mate: gives the normalized comparison mate and its invertibility; the first new task supplies its concrete ringed square input and the second compares fixed-A and ringed derived constructions.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-constant-derived-normalization-universal: the existing node concerns Constant derived realization preserves universal coefficient arrows; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-derived-adjunction-shift: the existing node concerns Canonical derived ringed-topos adjunction is shift-compatible; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-derived-scalar-extension-local-systems: the existing node concerns Coherent localized derived scalar extension and comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-finite-reduction-pullback-coherence: the existing node concerns Finite reduction and the canonical pullback square; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-flat-coefficient-reduction-adjunct: the existing node concerns Finite scalar comparison preserves derived reduction adjuncts; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-kflat-tensor-pullback-computation-universes: the existing node concerns Derived pullback computes K-flat tensor representatives; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-normalized-adjunction-square-transpose: the existing node concerns Transpose calculation for a normalized adjunction square with arbitrary comparison maps; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-normalized-derived-isomorphism-section-reduction: the existing node concerns Normalization-compatible evaluation of actual local Isom sheaves; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-normalized-derived-isomorphism-transport: the existing node concerns Universal normalization and evaluation of source-site local Isom sheaves; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-normalized-origin-comparison-coherence: the existing node concerns Comparison reduction respects canonical scalar units and composition; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-pullback-resolving-computation: the existing node concerns Derived pullback computes on resolving complexes with independent universes; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-pullback-tensor-canonical-shift-unit: the existing node concerns Canonical shifts and action units of the derived pullback tensor comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-pulled-reduction-normalization-comparison: the existing node concerns Successive quotient normalizations under the pulled reduction comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-reduction-pullback-derived-tower: the existing node concerns Normalized derived pullback of a strict coefficient reduction tower; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-resolving-representative-whiskering: the existing node concerns Restriction to resolving representatives is fully faithful; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-restriction-derived-products: the existing node concerns Exact scalar restriction on derived module sheaves is a right adjoint; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ring-sheaf-change-adjunction: the existing node concerns Derived adjunctions under compatible changes of ring sheaves; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-derived-slice-localization: the existing node concerns Derived slice compatibility and pullback of section localizations; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-equivalence-module-hom: the existing node concerns Module and closed Hom transport under a ringed equivalence; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-exchange-tensor-coherence: assumes a ringed square and its canonical operations and proves a projection/exchange identity; neither new lemma states that identity.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-projection-global-model: the existing node concerns Existence of the canonically normalized global projection package; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-projection-local-model: the existing node concerns Localization of a normalized global projection package; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-projection-mate-exact: constructs and proves exactness for the ringed projection transformation; it does not identify that construction with fixed-A module-valued sheaf adjunctions.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-projection-restriction: the existing node concerns Localization comparisons for the ringed projection mate; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-projection-tensor-comparison: the existing node concerns Descent and signed shifts of the normalized pro-etale tensor comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-projection-tensor-shifts: the existing node concerns Signed shifts of an already normalized tensor comparison; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-slice-comparisons-shift: the existing node concerns Shift normalization of canonical ringed-slice comparisons; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-slice-derived-comparisons: the existing node concerns Normalized derived direct-image slice comparison and invertibility of its mate; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-slice-derived-image-exists: the existing node concerns Existence of normalized total derived module adjunction; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-slice-derived-mate-isIso: the existing node concerns Invertibility of the normalized derived slice comparison mate; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-slice-evaluation-transpose: the existing node concerns Slice restriction preserves evaluation for an arbitrary dualizing object; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-slice-koszul-coherence: the existing node concerns Normalized slice restriction preserves Koszul exchange; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-slice-localization-model: the existing node concerns Ordinary single-complex model for pullback of section localization; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-slice-normalized-comparisons: the existing node concerns Existence of normalized slice tensor, Hom and Koszul comparisons; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-square-tensor-compatibility: assumes a supplied ringed tensor-square presentation and flat-term normalization; it proves a representative tensor equation, not existence/identification of this constant-A realization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: constructs a ringed pullback tensor isomorphism; it does not identify it with a separately constructed fixed-A module-valued sheaf model or construct the etale/proetale ringed square.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-existence: the existing node concerns Canonical tensor comparison unit existence; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-uniqueness: the existing node concerns Canonical tensor comparison unit uniqueness; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-site-module-sheaf-constant-ring-equivalence: gives an equivalence and ordinary constant-module normalizations, not a geometric square or the derived tensor/adjunction/projection identifications.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-strict-scalar-ordinary-adjoints-exist: the existing node concerns Normalized ordinary derived scalar adjunctions; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs lem-weil-pbc-tensor-comparison-descent-representatives: the existing node concerns Unique descent of tensor comparison from representatives; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs prop-weil-pbc-derived-inverse-image-adjunction: the existing node concerns Derived adjunction of inverse and direct image on D^+; it does not assert the fixed-A module-valued versus constant-ring sheaf derived realization with both tensor and counit/Plus normalization.

lem-sfb-constant-module-derived-projection-identification vs stage3-proetale-comparison-counit: asserts the already normalized comparison counit equation; the new tasks construct the ringed-square realization and compare the underlying derived coefficient models.

