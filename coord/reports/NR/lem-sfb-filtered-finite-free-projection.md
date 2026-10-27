## Worker report

Item: lem-sfb-filtered-finite-free-projection. Group: NR. Stage 1 only, direct delivery.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-filtered-finite-free-projection.json: split statement; eight proof steps; all dependencies reused from the current DAG; no Mathlib match for the whole item.
- citations.json: one verbatim statement quotation for each of the 21 node uses, numbered by proof step.
- report.md: this report. searches.jsonl contains the actual search-command records; write_split.py is sandbox-only working material and is not a DAG delivery file.

New nodes: 0. New Mathlib leaves: 0.

### Attachments

None for this item. Searched the project under lean/WeilConjectures by the exact blueprint tag and by projectionFormula, projection_formula, finite-free and filtered-projection terminology. Read the related finite-extension comparison in SixFunctors/ProEtale/ModuleObject/Colimit/Compatibility.lean, especially finitePush_of_pointCopower and isIso_derivedPushHom_padicSubfieldRingObjMap. These specialize to particular condensed coefficient changes and do not state this arbitrary module-diagram result with its cohomology/cocone clauses. The algebraic-closure comparison additionally assumes coproduct preservation and therefore cannot attach this item. Existing sorry declarations are not counted as completed proofs.

### WANTED

None. The Hemo–Richarz–Scholbach PDF, the current blueprint, Stacks sources and tags, and the relevant project sources are present.

### Corrections and scope

The imported node had no proof. Its mathematical statement is retained. Added inline definition references for flatness and D-plus and their two statement dependencies; these add no hypotheses. Retained its source, created metadata, original search history, and blueprint ancestry. Filled same_as after blueprint searches. No chapter or unit record is changed: this created helper is not its unit's key node.

The necessary continuity theorem must allow arbitrary ring sheaves. lem-weil-pbc-condensed-qcqs-pushforward-continuity assumes coefficients pulled from a condensed ring and is consequently too restrictive here. Instead the proof uses the already existing det-pe-bounded-continuity-direct-image, whose statement permits any ring sheaf on X. Its direct image has the natural f_*R_X action. Step 6 explicitly restricts that action along the actual R_Y -> f_*R_X unit to identify the direct image used in the item. It does not silently identify different module categories.

No assertion about arbitrary unbounded filtered systems or infinite coproducts is inferred. Only the strict complexes LP_i tensor K with one common degreewise lower bound enter direct-image continuity. The source-side tensor colimit is computed on a fixed representative and then on cohomology, rather than by assuming a derived-colimit theorem.

### Unfinished work

None at the level of this one-level split. Existing cited nodes keep their current status. This delivery creates no obligations on a new node.

## Not duplicates

No new nodes, so there are no new/existing same-tag pairs. Whole-blueprint searches were run for filtered finite free, projection colimit and bounded continuity, in addition to the whole-DAG statement/title searches for flat tensor, exact filtered colimits, bounded-below direct image, finite biproducts and cohomological detection. The existing tensor-colimit, arbitrary-ring continuity, canonical projection-mate and flat-normalization nodes are cited instead of duplicated. None of the blueprint hits states the full item. In particular, the perfect projection formula only covers the finite-free stages, not the general flat colimit B and its specified continuity/cocone description.

## Review by NR

I read the current chapter and sk-prop-open-coefficients unit, the ancestor lem-sfb-dc-lower-star-preserves and its proof, and the current bounded-continuity unit, including its arbitrary-ring complement. The assigned item serves the ancestor's final passage from finite coefficients to the algebraic closure. Its eight steps implement the prescribed filtered, uniformly bounded-below route. I read Hemo–Richarz–Scholbach Lemma 5.3(1), equation (5.4), PDF p. 14 and its proof, including the common-lower-bound requirement. I also read Stacks sites-cohomology.tex at equation-projection-formula-map (Tag 0B56) and lemma-projection-formula (Tag 0944), and sites-modules.tex at lemma-limits-colimits (03DB) and lemma-tensor-commute-colimits (03EP). Flat degree-zero tensor computation is the fixed-K-flat-factor construction preceding definition-derived-tor (06YU); I checked the flat-complex and K-flat-resolution passages as well. The proof_origin is agent: these sources supply the separate ingredients, while the explicit cocone assembly is written here. No prohibited route is used.

For step 1 I opened lem-weil-pbc-ringed-projection-mate-exact. Its statement gives precisely the natural canonical tensor comparison, the counit-normalized projection transformation and its value at the tensor unit. I wrote out the adjunct of both composites for an arbitrary u:P -> P', so the naturality claim includes every transition arrow and the original v_i rather than a newly chosen colimit cocone. The tensor symmetry changes only the order of factors, consistently with the item's definition.

For step 2 I checked the same node's exact-functor assertion and lem-sfb-left-resolution-additive-finite-coproducts, whose statement gives the canonical comparison for an additive functor and every finite family, including the empty family. I used def-weil-pbc-proetale-operations for additive K-injective direct image. Evaluating on each basis injection gives the actual finite-biproduct comparison; this proves its normalization, not just existence of an unrelated isomorphism. The finite-free argument is in the item itself rather than a new node restating a clause.

For step 3 I checked lem-pc-sheaf-modules-tensor-closed for tensor additivity and the unit, lem-pur-flat-single-derived-normalization for a flat degree-zero factor and an arbitrary unbounded other complex, and lem-pc-kflat-resolution for a fixed replacement. Flatness of finite free sheaves is written out from coordinatewise kernels/cokernels. The two flat colimit hypotheses are those already in the item. The flat-normalization statement is natural in the other factor; I therefore supplied the additional commuting square using a single replacement to verify maps in the varying flat factor, rather than attributing that extra assertion to the cited statement without an argument.

For step 4 I checked lem-pc-module-filtered-colimits-tensor: it explicitly supplies both exactness of filtered module-sheaf colimits and the total-tensor colimit comparison. I read src-weil-homology-preserves-exact-colimits and the corresponding DegreewiseLimits.lean statements at lines 76–89 and 142–144; its hypotheses are arbitrary abelian categories with exact colimits of the chosen shape. They hold here by the former node. The displayed lambda_q has legs H^q(v_i tensor 1), because these are the maps in the strict tensor cocone and the homology comparison is the canonical one.

For step 5 I checked def-sbc-standard-tstructure-derived-category, which explicitly characterizes the lower cohomology bound by existence of a strict representative zero below that degree. I read the full def-weil-pbc-proetale-operations statement for the exact cartesian module pullback. lem-weil-pbc-ringed-topos-pullback-filtered-colimits permits independently sized small sites and a coefficient-universe-small filtered category; those are exactly the size hypotheses here, and inverse-image presentations are available from the operations just specified. Applying the tensor-colimit node on X gives the pulled-back strict cocone. A degree-zero coefficient factor cannot introduce terms below a, so the common bound is literal termwise vanishing. This works for any K with such a bound, as the statement requests.

For step 6 I read det-pe-bounded-continuity-direct-image's complete statement and its source blueprint file, not merely its title. It takes a qcqs map, any source ring sheaf, and a strict filtered diagram zero below a fixed degree. Those are exactly f, R_X and D_i from step 5. I also read lem-weil-pbc-module-sheaves-colimits-forgetful, including its exactness and all-small-colimit clauses. Its sheafification hypothesis holds on the small sites in the item's coefficient universe. Restriction of scalars keeps the underlying complexes and their kernel/cokernel and colimit diagrams; the source K-injective resolution is the same in both direct-image formulas. This explicitly identifies the canonical comparison with rho_q and checks its actual legs. No property of a merely underlying abelian comparison is claimed to construct a new, unrelated R_Y-linear map.

Step 7 is elementary assembly from steps 1, 2, 4 and 6. Precomposition with each colimit injection gives the stated equation; the universal property gives equality of maps. Inverses of an invertible natural transformation form a natural transformation, so the induced colimit is invertible. The proof establishes the advertised formula for H^q(delta_B) as well as its invertibility.

For step 8 I checked prop-pur-kinjective-resolutions-exist for Grothendieck module-sheaf categories on arbitrary small ringed sites, lem-sp-grothendieck-enough-injectives for the general enough-injectives conclusion, and lem-weil-pbc-dplus-injective-representative for strict bounded-below injective K-injective representatives. The latter's main assertion is for an arbitrary abelian category with enough injectives; its etale example is not an extra restriction. The actual operations node computes G on those representatives by f_* degreewise, hence keeps a lower bound. The flat models keep a lower bound for both tensor vertices. Finally lem-weil-pbc-derived-plus-iso-on-cohomology explicitly states the criterion for an arbitrary abelian category; we have verified its D-plus hypothesis for both vertices before applying it. I did not apply a bounded-below criterion to unchecked unbounded objects.

I tested the statement and argument for rank zero, rank one, C=0, the zero coefficient ring, a constant singleton filtered diagram, noninjective transition maps, and diagrams with changing finite ranks and no compatible bases. Rank zero uses the zero biproduct, rank one is the unit/counit identity, and arbitrary transition maps are handled by naturality before any basis choice. The proof never requires injectivity of the v_i or transitions, finite presentation of B, a global cohomological dimension bound, or X and Y themselves to be qcqs. The map f is the qcqs input to the continuity theorem.

Against delivery-errors B–E I verified the statement/dependency references, single TeX escaping, blueprint ancestry, no new-node relabelling, no proof-of-a-node citations, and no extra hypotheses. citations.json contains a verbatim statement quote for every use. All non-elementary facts are existing cited nodes; the remaining coordinate and cocone arguments are written explicitly. Every proof step is under 2000 characters and none defers a hidden comparison to “standard” or “transport.” Generic off-unit categorical tools are declared with their individual reasons in split_report.tool_uses; the bounded-continuity theorem lies on the unit's prescribed route. No tools or repository files were edited, no agents were started, and no Lean or build command was run.
