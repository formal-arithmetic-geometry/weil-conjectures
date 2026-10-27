## Files written

- dag/nodes/sec-trace-formula/lem-trf-zariski-etale-functor-comparison-square.json: statement, split; Mathlib search finds general adjunction and pullback-composition tools, but no declaration of this complete mixed-site comparison.
- citations.json: a verbatim statement quotation for every node cited in each numbered step.
- No new DAG nodes; no new Mathlib leaves. Searches remain in searches.jsonl. No Lean written or compiler/build invoked.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for Zariski/etale module, comparison, pullback and pushforward terminology. Nearby ZariskiEtaleCore and EtaleZariskiQcohComparison concern site/cohomology comparisons, and do not state all the present functor-square and canonical flat-base-change section clauses. Existing sorry declarations are not attachments.

## WANTED

None. All mathematical sources used are available in literature/stacks-project.

## Findings and changes

The item's statement is retained verbatim, including its separated hypothesis and canonical map normalization. Its proof was empty. Filled it with seven steps, keeping all statement dependencies, import and ancestry fields. Read the current blueprint's sk-i-curve-zero statement and lem-trf-local-term-locality proof: the latter now concerns contracting correspondences, not this auxiliary module comparison. The item's historical chain through polarized ampleness descent remains explicit rather than pretending that the latest locality proof directly proves this fact. The parent scheme-Zariski-etale equivalence still cites precisely this item's two functorial clauses.

DAG/blueprint searches: searched all DAG statements/titles for flat base change, quasi-coherent direct image, the relevant Stacks tags, conjugate adjoints and module functors; ran blueprint_refs.py ancestor for the item and search for flat base change, quasi-coherent and Zariski/etale terminology. The existing pqf-lem-pushforward-qcoh and lem-pc-flat-base-change-cohom are the exact generic inputs, so no duplicates are created. The global-sections-qcqs node only treats the structure sheaf over affine bases; the proper-over-a-field coherent base-change node is too specialized. Neither was substituted for the general quasi-coherent base-change statement.

Read actual Mathlib hits in Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean (pullbackPushforwardAdjunction at line 60 and pullbackComp at line 167) and AlgebraicGeometry/Modules/Sheaf.lean (pushforward, its section formulas, pullbackPushforwardAdjunction). Those are general category/ringed-site constructions. They do not themselves state the mixed-site square or the quasi-coherent pushforward section isomorphism, so this item is not a Mathlib leaf. Recorded only actual msearch.py queries, including a second semantic phrasing. All services returned results; none was represented as unavailable or absent contrary to its output.

Generic off-unit tool uses are declared in split_report for lem-weil-pbc-ringed-topoi-module-adjunction and lem-weil-pbc-flat-base-change-map-sections. The former supplies the ordinary tensor adjunction, the latter the normalization of the canonical map. They do not replace any local-term unit step. Other off-unit categorical inputs are Mathlib leaves and the two coherent-sheaf input nodes are Lean-closed.

## Unfinished work

None in this stage-1 split. Existing unsplit inputs remain separate items, as required. No claim that those inputs are already proved is made.

## Not duplicates

No new nodes, hence no new/existing pairs to compare.

## Review by Q29

I read Stacks descent.tex Tag 03FH, label remark-change-topologies-ringed-sites, both parts, and Tag 03LC, label proposition-equivalence-quasi-coherent-functorial, its statement and full proof. Part 03FH(2) applies to arbitrary modules; quasi-coherence is needed only in 03LC(3). The latter assumes qcqs, so the present separated case is a valid specialization. I also read schemes.tex Tag 01LC, lemma-push-forward-quasi-coherent, coherent.tex Tag 02KH, lemma-flat-base-change-cohomology, cohomology.tex Tag 02N7, lemma-base-change-map-flat-case and its construction by lifting the adjunction unit, sites-modules.tex Tag 03D7, lemma-adjoint-pullback-pushforward-modules, categories.tex Tag 0B65, lemma-transformation-between-functors-and-adjoints, and spaces-morphisms.tex Tag 03M8, lemma-compute-pushforward. No forbidden SGA route is used.

Step 1 uses the actual statement of def-trf-space-etale-module-functors: its specified chart limit and projections, not an arbitrary direct-image functor. The etale base-change node ensures that U times_T V is itself a permitted chart. This is terminal in the chart category and initial in its opposite, the correct variance for the limit. A compatible family is exactly the restrictions of its component there; this proves the evaluation directly without a new limit lemma. The tensor-sections node states that R is restriction to open subschemes. Thus both right composites on W are literally G(a inverse W), with the same ring action and restrictions. I checked the scalar map factors through a_V sharp. This step is elementary relative to those statements.

Step 2 uses the tensor adjunction stated in the ringed-topoi-module-adjunction node and the Zariski adjunction in def-pc-module-pullback, then the composite-adjunction node's actual unit formula. The conjugate-iso-unit-equation node explicitly states the existence, uniqueness and invertibility with delta:R2 to R1. I checked L1=L_U a*, R1=a_*R_U and L2=a_et* L_T, R2=R_T a_et,*. The displayed unit equation has domain M and codomain R1 L2 M. Thus the direction of c and delta is correct and the comparison uses the specified adjunctions. No quasi-coherence enters.

Step 3 reads separatedness from the closed-diagonal clause of the item's definition node. The closed-immersion definition includes its affine characterization, and lem-weil-pbc-affine-scheme-qcqs supplies quasi-compactness of each affine inverse image, making this diagonal quasi-compact; the quasi-separated definition is exactly quasi-compactness of the diagonal. This verifies, rather than silently assumes, the qs hypothesis of pqf-lem-pushforward-qcoh. That statement says f_* preserves quasi-coherence for qcqs f. The statement of lem-pc-flat-base-change-cohom gives the actual base-change map as an isomorphism for all i, for a Cartesian square, qcqs f and flat g. Here f=a, g=v, f'=a_V, g'=v', i=0. Flatness of v is in def-weil-etale-morphism. No properness, Noetherian hypothesis or affine base is imported. Applying global sections to a sheaf isomorphism is elementary.

Step 4 uses the statement, not the proof, of lem-weil-pbc-flat-base-change-map-sections: in degree zero its transpose sends s to pullback of s along v'. Its two flatness hypotheses hold because v' is also etale by the cited base-change node and the etale definition includes flatness. The pullback and tensor definitions say why local generators b tensor s determine the sheaf map. The formula sends them to a_V sharp(b) times pullback(s), so comparison with a module map h is an equality on those generators. This fixes the canonical map, not just an arbitrary bijection of sections.

Step 5 checks test-object naturality explicitly. For q:V1 to V over T and Q on the fiber products, a_V Q=q a_V1. Both restriction paths send the local generator to the same scalar a_V1 sharp(q sharp b) times (v'Q)*s. The composition isomorphisms stated in def-pc-module-pullback are the ones used in the section-presheaf restrictions. The tensor sheaf definition allows equality to be checked on local generators. This is a routine calculation, not an unproved base-change theorem for q. In particular q need not be flat. I corrected the tempting but unnecessary claim that every map between test objects would need a separate flatness argument: this calculation uses none.

Step 6 uses precisely the section and scalar/restriction clauses of lem-trf-etale-extension-free-presentations-hom, for the already-proved quasi-coherent a_*H and for H. Since U_V is etale over U, its section formula is applicable. Step 1 supplies the target direct-image evaluation. Steps 4/5 supply morphism compatibility; inverse component maps obey the inverse naturality equation by cancellation. There is no appeal to the parent's equivalence (which depends on the item), and no cycle: checked all cited inputs' transitive dependencies for a path back to this item.

Step 7 reads the open-immersion-module-pullback-restriction statement, including its unit equation, for W and its inverse-image open. Both section modules become Gamma(a inverse W,H); the normalized generator 1 tensor s maps to s. The free-presentations-hom node explicitly gives the same open unit normalization. This proves the identity clause rather than merely saying it transports. The step is elementary with those normalization statements.

Small cases checked: a=id (both comparisons reduce to their unit-compatible identities); an open test W, including the empty open (identity on the zero section module); H=0; empty U or T whenever a exists; an etale test V with non-quasi-compact source (02KH needs a qcqs, not V qc); arbitrary non-quasi-coherent M in the left-adjoint square; non-proper qc separated a; an arbitrary test-object arrow q. The module assertion is on the small etale site, not all base changes on a big site: 03LC's counterexample A2 minus the origin over A2 at the origin does not contradict it, because that test map is not etale/flat. All seven steps are below 2000 characters. No new node is a clause relabeling, elementary lemma, duplicate or unsearched Mathlib result, because no new nodes are introduced.

Validation: the first server dry run passed. Final self-review then added the existing Mathlib leaf lem-weil-pbc-affine-scheme-qcqs to step 3 and its verbatim citation, making the affine-implies-quasi-compact input explicit. Re-running preflight on this final version.
