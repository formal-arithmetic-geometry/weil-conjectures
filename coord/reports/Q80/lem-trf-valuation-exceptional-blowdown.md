# Worker report — Q80 — repair of returned head ce789cec79

## Files written

The item `dag/nodes/sec-trace-formula/lem-trf-valuation-exceptional-blowdown.json` is split into eight steps. Its statement, statement dependencies, source, unit and blueprint ancestry are unchanged from the current shared repository. I compared the retained sandbox item with the current repository: only its split-owned proof, status, proof-origin, searches and split-report fields differ. The current shared item remains unsplit. The delivery tool rebases the submitted split-owned fields onto the current server base; no manual git command was run.

Four new statement-only nodes are retained: `lem-trf-valuation-curve-projective-preparation` (normalization, compactification, locality), `lem-trf-valuation-nodal-polar-section` (divisors and a section), `lem-trf-valuation-normalized-graph-model` (graph image, normal factorization, connected fibres), and `lem-trf-valuation-exceptional-local-criterion` (open semistable locus and reduced-fibre exceptional-tree criterion). All remain unsplit, with no Mathlib match; there are no new Mathlib leaves. The graph and local-criterion statements and the item's Steps 6–7 were substantively repaired. `citations.json` was regenerated for all 13 uses in eight steps. The earlier report and citation evidence are retained as `report-before-e2-repair.md` and `citations-before-e2-repair.json` in this sandbox, The previous report is archived in the sandbox; its unchanged source, search and duplicate evidence has been retained in this report.

## Attachments

None. The exact item tag and blowdown/Temkin/semistable terminology were searched under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/`. No project declaration states the contraction theorem. The previous attachment and new-node searches remain valid for the unchanged inputs; no upstream sorry declaration was counted as finished.

## Literature wanted

WANTED: `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, Lemmas 4.4.1, 4.4.2, 4.4.5, Proposition 4.4.6, Lemma 5.1(i), and Appendix B (especially Corollary B.2), for this item and its four new nodes. The archival PDF is absent from the shared literature. I read the primary source online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf without downloading a file. The item retains agent proof provenance. There is no SGA citation.

## Repair of E2/C4 — statement disputed and corrected

STATEMENT-DISPUTED: the returned normalized-graph statement asserted that all associated points of every positive-dimensional geometric fibre have dimension one. The reviewer's cusp-contraction fibre has completed local ring

$R=\mathbf C[[r,v]]/(rv,v^2)$.

The nonzero class of $v$ has annihilator $(r,v)$: writing a class as $a(r)+cv$ shows that multiplying by $v$ gives $a(0)v$. Thus the closed maximal ideal is an embedded associated prime, of dimension zero, while the unique minimal prime is $(v)$ and $R_{\mathrm{red}}=\mathbf C[[r]]$. This explicitly refutes the old clause. It also exhibits why the underlying fibre can remain one connected curve even when there is embedded scheme structure. I accept the return; Temkin never asserts the deleted clause.

I deleted the entire positive-fibre purity assertion from `lem-trf-valuation-normalized-graph-model`. I did not replace it by an unsupported claim about associated points. Step 6 now uses only the node's connectedness and positive-dimensional modification-fibre statements. The source fibre is of finite type over a residue field, hence Noetherian, and its closed inverse image has finitely many irreducible components. The two existing Mathlib leaves `lem-weil-pbc-finite-type-over-noetherian` and `lem-weil-pbc-noetherian-finitely-many-components` are cited for exactly these facts. Every one-dimensional irreducible component is a contracted component of the source base fibre; properness of f1 and Step 4 force it to be Z. A zero-dimensional *irreducible component* would be a singleton disjoint from every other irreducible component (otherwise it is not maximal irreducible), and the finite component decomposition would make it open and closed. Connectedness excludes such an extra component. This proves only |F|=|Z|, hence F_red=Z; embedded associated points on Z are fully allowed.

Step 7 applies the reduced-fibre exceptional-tree criterion, then openness. The local-criterion node now explicitly speaks of the reduced subcurve inside the semistable source fibre, permits nilpotents and embedded associated points in F, and no longer claims that reduction itself preserves a scheme's nodal local rings. Its hypothesis is pure *topological* dimension one for Z, not purity of all associated primes of F. This is the criterion used in Temkin 4.4.2 and its proof: compactify, arrange geometrically reduced base fibres, compare their genera, and use Corollary B.2, whose genus formula sums source-curve components and source singularities on the inverse-image support. It is not an argument that scheme-theoretic reduction preserves nodal singularities. The tree, boundary branches and marking incidence are computed on the reduced subcurve of that source fibre. The parent now supplies precisely that object. The item statement and its closed-image convention are unchanged.

The archived historical report contains the prior, rejected purity repair; its mathematical claims are superseded by this repair and the current node/citation files.

## Searches and source audit for this repair

I read all previous recorded search results in `searches.jsonl` and retained their tool/query texts. For the changed graph and reduced-support criterion I ran fresh msearch.py LeanFinder, LeanSearch and grep searches with the corrected mathematical questions, and a valid quoted Loogle normalization query. The hits were general relative normalization and its universal property, definitions/instances for already-geometrically-connected morphisms, and unrelated Weierstrass reduction results. I opened `Mathlib/AlgebraicGeometry/Normalization.lean` around lines 340–415 and `Geometrically/Connected.lean` around lines 45–75: these do not give the valuation-curve finite normalized graph and normal-target connectedness theorem. LeanSearch also returned the existing finite-component theorem; I reuse its existing DAG leaf instead of creating a duplicate. A second graph phrasing and the earlier second semistability phrasing give no match. Exact queries and actual verdicts are appended to the two changed new nodes; no unavailable service is called a negative match.

I reran whole-blueprint searches for exceptional tree, normalized graph, polar and semistable locus (no equivalent blueprint nodes), read the current `lem-trf-local-term-locality` ancestor and `sk-i-curve-zero` unit, and searched the DAG for Temkin 4.4.2/4.4.5 and graph/connected-fibre terminology. These inputs refine the retained item, not a new alteration route. The two Noetherian inputs are existing Mathlib leaves and therefore generic tools allowed across units. The new same-source definitions listed by the initial dry run were opened and distinguished below. No new node is a restatement of the contraction conclusion; the map u and its component test are still proved in the parent.

## Review by Q80

I read the current item, all four new statements, and every existing statement cited in the eight steps, and checked them against Temkin's standing finite-height, separably closed valuation hypotheses. For projective preparation I read Lemma 4.4.1(i),(ii) and the local reduction of Proposition 4.4.6 (printed pp. 30, 32); for the polar input, its horizontal-divisor and lifted-section argument on pp. 32–33; for the graph input, the normalized relative-image construction on p. 33, together with the normal-target connectedness argument in 4.4.2 and finite-modification argument of 4.2.1; for the local criterion, Lemma 4.4.2, Appendix B/Corollary B.2 and Lemma 5.1(i). The source gives none of the old associated-point purity statement. The current helpers all have complete object/hypothesis statements, definition references or inline meanings, empty proof/proof_deps and null proof_origin, current blueprint ancestry and real search records.

Step 1 uses `lem-trf-geometrically-reduced-eta-normal` for reducedness and eta-normality over the normal affine base and `lem-trf-valuation-curve-projective-preparation` for finite normalization, normal-source factorization and localization/compactification. I checked both statements: eta-normality plus finite normalization gives source normality before the graph input is used. The finite-target replacement preserves closedness in both directions, so it does not alter B. The compactification is only required semistable near Z.

Steps 2–3 use the polar-section statement for the disjoint horizontal Cartier divisors, their smooth special points, the nonvanishing section a and canonical section e. Their common zero set has empty closed fibre, so properness over a local base makes it empty. The chart formula [e:a] constructs u; the elementary Laurent-polynomial argument makes it constant on Z, and the prescribed poles make it nonconstant on each other prepared closed-fibre component. The polar node does not assume or assert the desired contraction.

Step 4 uses the graph node for the normal intermediate eta-modifications, factorization, contraction test and isomorphism on the original isomorphism locus; the preparation node supplies restriction/spreading/gluing. I checked that the graph is restricted back before using the original smooth-generic-fibre hypotheses. Components with different closed images are outside the local support, and those over x other than Z have the nonconstant u established in Step 3. Step 5 uses exactly the horizontal-model statement's flat schematic generic-marking closure and uniqueness, on Y1 and on Y, to obtain both maps of pairs.

Step 6 uses the corrected graph statement and the two existing Noetherian Mathlib-leaf statements. The latter say respectively that finite type over a Noetherian scheme is Noetherian and that a Noetherian scheme has finitely many irreducible components. A field is Noetherian since its only ideals are zero and the whole field. The topological argument from this finite decomposition and connectedness is written out in the step, so no auxiliary lemma is hidden in a new node. Positive-dimensional closed subsets of a pure one-dimensional fibre are unions of its curve components; every other irreducible component is a closed point. The proof only excludes isolated extra *components*, never embedded associated points. Properness of f1 is used exactly to put the contracted curve's generic point in the original B set.

Step 7 uses the corrected local-criterion statement's semistability test and openness. Its normal-target, eta-modification-of-pairs and semistable-source hypotheses have already been verified. The point is closed, so it is closed in its base fibre. Its reduced inverse fibre is precisely the exceptional smooth P1 of Step 6, with no internal self-node and at most two boundary plus marking points. The source semistability and these conditions are what the criterion requires; no reducedness of F is assumed. Outside the modification locus h is an isomorphism; Step 5 identifies the markings there. The final quasi-compact T0 closed-point argument is stated explicitly.

Step 8 uses the final sentence of `lem-trf-finite-fibre-valuation-domination`, which explicitly states that a reduced modification of a normal target with smooth generic fibre is an isomorphism near every target fibre generic point. I checked that Y1 is normal with unchanged smooth generic fibre and Y is reduced. The proper image of a noncontracted component is a whole component of the pure one-dimensional target fibre. This yields the bijection on noncontracted fibre generic points, and f1 h=f preserves the original closed-image condition. Step 4 removes exactly z.

Small-case checks: the cusp local ring above is allowed by the corrected graph statement and disproves the removed clause; it creates no new topological component. A curve plus an isolated point would contradict the connectedness hypothesis, whereas an embedded point supported on the curve does not. Identity modifications and constant u recover the original normal graph model. Height zero gives no exceptional B point. Empty marking, a rational tail, a rational bridge and a rational component with two marking points satisfy the relevant at-most-two test; a looped component or a third special point fails exceptionality. No rank-one, Noetherian-total-space, proper-original-target or separated-original-target hypothesis was added. All eight steps are shorter than 2000 characters. This addresses the single E2/C4 return point by deleting the false helper clause, replacing its use by a proved reduced-support argument, and regenerating the exact citations. The four remaining unsplit helpers are the intended next level, not unfinished parent proof steps.

## Not duplicates

lem-trf-valuation-curve-projective-preparation vs lem-trf-valuation-horizontal-curve-models: the existing node gives flatness and generic marking closures for reduced modifications; it gives neither finite full normalization, normal projective compactification nor local extension of intermediate diagrams.

lem-trf-valuation-curve-projective-preparation vs lem-trf-geometrically-reduced-eta-normal: eta-normality and geometrically reduced fibres are not full normality or a normal projective compactification and do not state the required localization/gluing assertion.

lem-trf-valuation-curve-projective-preparation vs lem-trf-finite-fibre-valuation-domination: the existing node's final fibre-generic isomorphism clause is reused; it does not supply projective compactification or the locality of the construction.

lem-trf-valuation-nodal-polar-section vs lem-trf-valuation-exceptional-blowdown: the new node constructs divisors and a section only, independently of any contraction or modification f; the parent explicitly constructs its projective-line map and proves which components are contracted.

lem-trf-valuation-normalized-graph-model vs lem-trf-valuation-component-factorization: the existing theorem factors an already-given pair of models under a component-inclusion hypothesis; it constructs no normalized image from a projective-line map. Its eta-normal factorization conclusion does not give the new model or the connected-fibre statement.

lem-trf-valuation-normalized-graph-model vs lem-weil-pbc-scheme-theoretic-image-proper: the latter gives properness and surjectivity of a schematic image, not finite normalization, normal curve structure, an eta-modification factorization or its connected-fibre and contraction tests.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-valuation-exceptional-closed-image-criterion: the existing statement detects stability using the finite set of exceptional closed-image components; the new statement tests semistability of a normal target at one contraction point using its fibre tree. Neither implies the other by substitution.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-valuation-contracted-component-inclusion: the existing node compares contracted components of semistable and stable models; it does not state a target semistability criterion or openness.

lem-trf-valuation-normalized-graph-model vs lem-trf-proper-birational-curve-finite: the existing finite-morphism theorem concerns one-dimensional schemes of finite type over a field. These total valuation-ring curve models are not in that category and a graph contraction is not finite.

lem-trf-valuation-curve-projective-preparation vs lem-trf-valued-curve-etale-parameter: the existing statement finds an etale rational parameter for one valued one-variable function field; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-valued-curve-etale-parameter: the existing statement finds an etale rational parameter for one valued one-variable function field; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-valued-curve-etale-parameter: the existing statement finds an etale rational parameter for one valued one-variable function field; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-valued-curve-etale-parameter: the existing statement finds an etale rational parameter for one valued one-variable function field; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-stable-modification-finite-presentation-spread: the existing statement spreads a prescribed valuation-ring pair of proper generic isomorphisms to a quasi-model of a finite-type base; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-stable-modification-finite-presentation-spread: the existing statement spreads a prescribed valuation-ring pair of proper generic isomorphisms to a quasi-model of a finite-type base; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-stable-modification-finite-presentation-spread: the existing statement spreads a prescribed valuation-ring pair of proper generic isomorphisms to a quasi-model of a finite-type base; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-stable-modification-finite-presentation-spread: the existing statement spreads a prescribed valuation-ring pair of proper generic isomorphisms to a quasi-model of a finite-type base; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-strict-semistable-model-normal: the existing statement proves normality for a strictly semistable curve from its etale nodal charts; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-strict-semistable-model-normal: the existing statement proves normality for a strictly semistable curve from its etale nodal charts; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-strict-semistable-model-normal: the existing statement proves normality for a strictly semistable curve from its etale nodal charts; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-strict-semistable-model-normal: the existing statement proves normality for a strictly semistable curve from its etale nodal charts; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-valuation-exceptional-closed-image-criterion: the existing statement detects stability by the absence of exceptional closed-image components; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-valuation-exceptional-closed-image-criterion: the existing statement detects stability by the absence of exceptional closed-image components; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-valuation-exceptional-closed-image-criterion: the existing statement detects stability by the absence of exceptional closed-image components; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-curve-projective-preparation vs def-trf-multipointed-curve: the existing statement defines flat finitely presented pairs of relative dimensions one and zero, without any construction theorem; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs def-trf-multipointed-curve: the existing statement defines flat finitely presented pairs of relative dimensions one and zero, without any construction theorem; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs def-trf-multipointed-curve: the existing statement defines flat finitely presented pairs of relative dimensions one and zero, without any construction theorem; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs def-trf-multipointed-curve: the existing statement defines flat finitely presented pairs of relative dimensions one and zero, without any construction theorem; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-semistable-marked-base-change: the existing statement preserves multipointed semistability and fibrewise stability under arbitrary base change; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-semistable-marked-base-change: the existing statement preserves multipointed semistability and fibrewise stability under arbitrary base change; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-semistable-marked-base-change: the existing statement preserves multipointed semistability and fibrewise stability under arbitrary base change; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-semistable-marked-base-change: the existing statement preserves multipointed semistability and fibrewise stability under arbitrary base change; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-valuation-semistable-dominates-stable: the existing statement maps a given semistable model to a given stable one over any finite-height valuation field; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-valuation-semistable-dominates-stable: the existing statement maps a given semistable model to a given stable one over any finite-height valuation field; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-valuation-semistable-dominates-stable: the existing statement maps a given semistable model to a given stable one over any finite-height valuation field; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-valuation-semistable-dominates-stable: the existing statement maps a given semistable model to a given stable one over any finite-height valuation field; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-valuation-semistable-stable-contraction: the existing statement contracts a semistable modification all the way to a stable one and is an ancestor of this item; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-valuation-semistable-stable-contraction: the existing statement contracts a semistable modification all the way to a stable one and is an ancestor of this item; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-valuation-semistable-stable-contraction: the existing statement contracts a semistable modification all the way to a stable one and is an ancestor of this item; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-valuation-semistable-stable-contraction: the existing statement contracts a semistable modification all the way to a stable one and is an ancestor of this item; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-stable-modification-stability-locus: the existing statement refines a finite-type base so that an already-existing family which is stable at the specified valuation becomes stable; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-stable-modification-stability-locus: the existing statement refines a finite-type base so that an already-existing family which is stable at the specified valuation becomes stable; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-stable-modification-stability-locus: the existing statement refines a finite-type base so that an already-existing family which is stable at the specified valuation becomes stable; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-stable-modification-stability-locus: the existing statement refines a finite-type base so that an already-existing family which is stable at the specified valuation becomes stable; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-valuation-common-strict-semistable-refinement: the existing statement dominates two existing models by a common strictly semistable pair; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-valuation-common-strict-semistable-refinement: the existing statement dominates two existing models by a common strictly semistable pair; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-valuation-common-strict-semistable-refinement: the existing statement dominates two existing models by a common strictly semistable pair; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-valuation-common-strict-semistable-refinement: the existing statement dominates two existing models by a common strictly semistable pair; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-valuation-strict-semistable-cofinality: the existing statement dominates an arbitrary modification of a strict model by a strictly semistable model; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-valuation-strict-semistable-cofinality: the existing statement dominates an arbitrary modification of a strict model by a strictly semistable model; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-valuation-strict-semistable-cofinality: the existing statement dominates an arbitrary modification of a strict model by a strictly semistable model; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-valuation-strict-semistable-cofinality: the existing statement dominates an arbitrary modification of a strict model by a strictly semistable model; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-single-valuation-semistable-extraction: the existing statement makes a chosen closed-centred valuation fibre-generic on a strictly semistable modification; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-single-valuation-semistable-extraction: the existing statement makes a chosen closed-centred valuation fibre-generic on a strictly semistable modification; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-single-valuation-semistable-extraction: the existing statement makes a chosen closed-centred valuation fibre-generic on a strictly semistable modification; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-single-valuation-semistable-extraction: the existing statement makes a chosen closed-centred valuation fibre-generic on a strictly semistable modification; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-abhyankar-inequality: the existing statement bounds residue transcendence degree plus value-group rational rank by field transcendence degree; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-abhyankar-inequality: the existing statement bounds residue transcendence degree plus value-group rational rank by field transcendence degree; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-abhyankar-inequality: the existing statement bounds residue transcendence degree plus value-group rational rank by field transcendence degree; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-abhyankar-inequality: the existing statement bounds residue transcendence degree plus value-group rational rank by field transcendence degree; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-valuation-height-rank: the existing statement bounds lengths of valuation prime chains by value-group rational rank; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-valuation-height-rank: the existing statement bounds lengths of valuation prime chains by value-group rational rank; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-valuation-height-rank: the existing statement bounds lengths of valuation prime chains by value-group rational rank; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-valuation-height-rank: the existing statement bounds lengths of valuation prime chains by value-group rational rank; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-valuative-domination-eta-normal: the existing statement descends a factorization known after every finite-height valuation base change to an eta-normal model; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-valuative-domination-eta-normal: the existing statement descends a factorization known after every finite-height valuation base change to an eta-normal model; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-valuative-domination-eta-normal: the existing statement descends a factorization known after every finite-height valuation base change to an eta-normal model; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-valuative-domination-eta-normal: the existing statement descends a factorization known after every finite-height valuation base change to an eta-normal model; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-valuation-component-factorization: the existing statement factors already-given models under an inclusion of contracted components and eta-normality; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-valuation-component-factorization: the existing statement factors already-given models under an inclusion of contracted components and eta-normality; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-valuation-component-factorization: the existing statement factors already-given models under an inclusion of contracted components and eta-normality; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-marked-nodal-dualizing-degrees: the existing statement constructs the marked dualizing line and computes its degrees, for a stable modification over a Noetherian base; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-marked-nodal-dualizing-degrees: the existing statement constructs the marked dualizing line and computes its degrees, for a stable modification over a Noetherian base; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-marked-nodal-dualizing-degrees: the existing statement constructs the marked dualizing line and computes its degrees, for a stable modification over a Noetherian base; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-marked-nodal-dualizing-degrees: the existing statement constructs the marked dualizing line and computes its degrees, for a stable modification over a Noetherian base; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-valuation-strict-semistable-local-uniformization: the existing statement covers all centred valuations by integral strictly semistable birational quasi-models; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-valuation-strict-semistable-local-uniformization: the existing statement covers all centred valuations by integral strictly semistable birational quasi-models; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-valuation-strict-semistable-local-uniformization: the existing statement covers all centred valuations by integral strictly semistable birational quasi-models; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-valuation-strict-semistable-local-uniformization: the existing statement covers all centred valuations by integral strictly semistable birational quasi-models; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-prime-field-valuation-rank: the existing statement bounds the rational rank of a prime-field valuation by one; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-prime-field-valuation-rank: the existing statement bounds the rational rank of a prime-field valuation by one; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-prime-field-valuation-rank: the existing statement bounds the rational rank of a prime-field valuation by one; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-prime-field-valuation-rank: the existing statement bounds the rational rank of a prime-field valuation by one; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-abhyankar-finite-type-field-height: the existing statement bounds valuation height for finitely generated fields by transcendence degree; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-abhyankar-finite-type-field-height: the existing statement bounds valuation height for finitely generated fields by transcendence degree; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-abhyankar-finite-type-field-height: the existing statement bounds valuation height for finitely generated fields by transcendence degree; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-abhyankar-finite-type-field-height: the existing statement bounds valuation height for finitely generated fields by transcendence degree; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-nodal-polar-section vs lem-trf-valuation-horizontal-curve-models: the existing statement gives the T-curve structure of reduced modifications and uniqueness of flat generic-marking closures; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-valuation-horizontal-curve-models: the existing statement gives the T-curve structure of reduced modifications and uniqueness of flat generic-marking closures; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-valuation-horizontal-curve-models: the existing statement gives the T-curve structure of reduced modifications and uniqueness of flat generic-marking closures; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-valuation-exceptional-blowdown: the existing statement asserts existence of a semistable contraction of one specified exceptional closed-image component with a B-set bijection; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-normalized-graph-model vs lem-trf-valuation-exceptional-blowdown: the existing statement asserts existence of a semistable contraction of one specified exceptional closed-image component with a B-set bijection; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-valuation-exceptional-blowdown: the existing statement asserts existence of a semistable contraction of one specified exceptional closed-image component with a B-set bijection; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-birational-riemann-zariski-neighbourhoods: the existing statement gives compactness, open valuation neighbourhoods and a filtered presentation of a valuation ring; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-birational-riemann-zariski-neighbourhoods: the existing statement gives compactness, open valuation neighbourhoods and a filtered presentation of a valuation ring; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-birational-riemann-zariski-neighbourhoods: the existing statement gives compactness, open valuation neighbourhoods and a filtered presentation of a valuation ring; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-birational-riemann-zariski-neighbourhoods: the existing statement gives compactness, open valuation neighbourhoods and a filtered presentation of a valuation ring; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-valuation-contracted-component-inclusion: the existing statement compares component contraction sets in a common semistable model of a semistable and a stable model; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-valuation-contracted-component-inclusion: the existing statement compares component contraction sets in a common semistable model of a semistable and a stable model; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-valuation-contracted-component-inclusion: the existing statement compares component contraction sets in a common semistable model of a semistable and a stable model; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-nodal-polar-section vs lem-trf-finite-fibre-valuation-domination: the existing statement tests domination with finitely many valuations and asserts isomorphisms near target fibre generic points; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-finite-fibre-valuation-domination: the existing statement tests domination with finitely many valuations and asserts isomorphisms near target fibre generic points; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-finite-fibre-valuation-domination: the existing statement tests domination with finitely many valuations and asserts isomorphisms near target fibre generic points; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-marked-curve-finite-type-model: the existing statement descends an existing multipointed family to an integral base of finite type over Z; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-marked-curve-finite-type-model: the existing statement descends an existing multipointed family to an integral base of finite type over Z; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-marked-curve-finite-type-model: the existing statement descends an existing multipointed family to an integral base of finite type over Z; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-marked-curve-finite-type-model: the existing statement descends an existing multipointed family to an integral base of finite type over Z; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-nodal-polar-section vs lem-trf-geometrically-reduced-eta-normal: the existing statement proves reducedness and eta-normality, which by itself is not full normality or a projective model; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-geometrically-reduced-eta-normal: the existing statement proves reducedness and eta-normality, which by itself is not full normality or a projective model; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-geometrically-reduced-eta-normal: the existing statement proves reducedness and eta-normality, which by itself is not full normality or a projective model; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-valuation-stable-reduction: the existing statement asserts stable reduction over the valuation ring and is an ancestor of this item; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-valuation-stable-reduction: the existing statement asserts stable reduction over the valuation ring and is an ancestor of this item; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-valuation-stable-reduction: the existing statement asserts stable reduction over the valuation ring and is an ancestor of this item; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-valuation-stable-reduction: the existing statement asserts stable reduction over the valuation ring and is an ancestor of this item; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-stable-modification-uniqueness-normal: the existing statement identifies two stable modifications uniquely over a normal base; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-stable-modification-uniqueness-normal: the existing statement identifies two stable modifications uniquely over a normal base; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-stable-modification-uniqueness-normal: the existing statement identifies two stable modifications uniquely over a normal base; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-stable-modification-uniqueness-normal: the existing statement identifies two stable modifications uniquely over a normal base; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-stable-modification-spreading: the existing statement spreads an already-prescribed stable valuation model to a quasi-alteration; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-stable-modification-spreading: the existing statement spreads an already-prescribed stable valuation model to a quasi-alteration; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-stable-modification-spreading: the existing statement spreads an already-prescribed stable valuation model to a quasi-alteration; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-stable-modification-spreading: the existing statement spreads an already-prescribed stable valuation model to a quasi-alteration; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-no-isolated-contracted-fibre-component: the existing statement excludes contraction of an isolated whole proper connected geometric-fibre component over a Noetherian base; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-no-isolated-contracted-fibre-component: the existing statement excludes contraction of an isolated whole proper connected geometric-fibre component over a Noetherian base; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-no-isolated-contracted-fibre-component: the existing statement excludes contraction of an isolated whole proper connected geometric-fibre component over a Noetherian base; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-no-isolated-contracted-fibre-component: the existing statement excludes contraction of an isolated whole proper connected geometric-fibre component over a Noetherian base; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-valuation-marking-semistable-separation: the existing statement modifies a strictly semistable underlying curve so that a given generic marking becomes semistable; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-valuation-marking-semistable-separation: the existing statement modifies a strictly semistable underlying curve so that a given generic marking becomes semistable; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-valuation-marking-semistable-separation: the existing statement modifies a strictly semistable underlying curve so that a given generic marking becomes semistable; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-valuation-marking-semistable-separation: the existing statement modifies a strictly semistable underlying curve so that a given generic marking becomes semistable; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-riemann-zariski-finite-refinement: the existing statement gives finite valuation-space refinements of proper and quasi-models of the base; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-riemann-zariski-finite-refinement: the existing statement gives finite valuation-space refinements of proper and quasi-models of the base; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-riemann-zariski-finite-refinement: the existing statement gives finite valuation-space refinements of proper and quasi-models of the base; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-riemann-zariski-finite-refinement: the existing statement gives finite valuation-space refinements of proper and quasi-models of the base; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-valuation-algebraic-height: the existing statement identifies ordered prime spectra of a valuation ring and its restriction across an algebraic field extension; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-valuation-algebraic-height: the existing statement identifies ordered prime spectra of a valuation ring and its restriction across an algebraic field extension; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-valuation-algebraic-height: the existing statement identifies ordered prime spectra of a valuation ring and its restriction across an algebraic field extension; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-valuation-algebraic-height: the existing statement identifies ordered prime spectra of a valuation ring and its restriction across an algebraic field extension; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-birational-quasi-modification-common-cover: the existing statement produces a common proper refinement from a covering by birational quasi-modifications; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-birational-quasi-modification-common-cover: the existing statement produces a common proper refinement from a covering by birational quasi-modifications; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-birational-quasi-modification-common-cover: the existing statement produces a common proper refinement from a covering by birational quasi-modifications; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-birational-quasi-modification-common-cover: the existing statement produces a common proper refinement from a covering by birational quasi-modifications; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-nodal-normalization-adjunction: the existing statement normalizes one nodal field-curve component and computes its adjunction twist; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-nodal-normalization-adjunction: the existing statement normalizes one nodal field-curve component and computes its adjunction twist; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-nodal-normalization-adjunction: the existing statement normalizes one nodal field-curve component and computes its adjunction twist; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-nodal-normalization-adjunction: the existing statement normalizes one nodal field-curve component and computes its adjunction twist; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-stable-curve-diagram-noetherian-model: the existing statement descends a finite already-existing diagram of semistable modifications to a normal finite-type base; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-stable-curve-diagram-noetherian-model: the existing statement descends a finite already-existing diagram of semistable modifications to a normal finite-type base; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-stable-curve-diagram-noetherian-model: the existing statement descends a finite already-existing diagram of semistable modifications to a normal finite-type base; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-stable-curve-diagram-noetherian-model: the existing statement descends a finite already-existing diagram of semistable modifications to a normal finite-type base; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs lem-trf-normal-approximation-finite-eta-modification: the existing statement descends an already finite eta-modification of a geometrically reduced family to a normal Noetherian base; the new statement instead supplies finite normalization, a normal projective compactification, and locality/gluing of intermediate diagrams; it asserts no exceptional contraction.

lem-trf-valuation-nodal-polar-section vs lem-trf-normal-approximation-finite-eta-modification: the existing statement descends an already finite eta-modification of a geometrically reduced family to a normal Noetherian base; the new statement instead supplies horizontal Cartier divisors and a section with exact poles on the other fibre components; it constructs no new curve model.

lem-trf-valuation-normalized-graph-model vs lem-trf-normal-approximation-finite-eta-modification: the existing statement descends an already finite eta-modification of a geometrically reduced family to a normal Noetherian base; the new statement instead constructs a normal intermediate curve from an arbitrary map to P1 and tests its contractions; it neither chooses such a map nor asserts semistability.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-normal-approximation-finite-eta-modification: the existing statement descends an already finite eta-modification of a geometrically reduced family to a normal Noetherian base; the new statement instead tests semistability at a normal contraction point by its reduced fibre tree and gives openness; it asserts no contraction exists.

lem-trf-valuation-curve-projective-preparation vs def-trf-modification: the existing definition only defines a modification; this node states finite normalization, geometrically reduced fibres, normal projective preparation, and locality/gluing over a valuation curve.

lem-trf-valuation-curve-projective-preparation vs def-trf-multipointed-curve-modification: the existing definition only defines modifications of multipointed curves; this node proves normalization, compactification, and local extension properties.

lem-trf-valuation-curve-projective-preparation vs def-trf-rational-rank: the existing definition concerns valuation rank; this node concerns relative curve normalization and projective preparation.

lem-trf-valuation-curve-projective-preparation vs def-trf-schematically-dense-open: the existing definition only defines schematic density; this node uses that notion in a normalization and gluing theorem.

lem-trf-valuation-curve-projective-preparation vs def-trf-strict-semistable-curve: the existing definition only defines strict semistability; this node gives normalization and projective preparation for arbitrary T-curves.

lem-trf-valuation-curve-projective-preparation vs def-trf-strictly-semistable-curve: the existing definition only defines strict semistability; this node gives normalization and projective preparation for arbitrary T-curves.

lem-trf-valuation-exceptional-local-criterion vs def-trf-modification: the existing definition only defines a modification; this node characterizes semistability at a contraction point by an exceptional projective-line tree.

lem-trf-valuation-exceptional-local-criterion vs def-trf-multipointed-curve-modification: the existing definition only defines multipointed modifications; this node proves the local exceptional-tree criterion.

lem-trf-valuation-exceptional-local-criterion vs def-trf-rational-rank: the existing definition concerns valuation rank; this node concerns semistability and exceptional fibres.

lem-trf-valuation-exceptional-local-criterion vs def-trf-schematically-dense-open: the existing definition only defines schematic density; this node proves a semistability criterion for an eta-modification.

lem-trf-valuation-exceptional-local-criterion vs def-trf-strict-semistable-curve: the existing definition only defines strict semistability; this node gives an iff criterion for ordinary semistability after contraction.

lem-trf-valuation-exceptional-local-criterion vs def-trf-strictly-semistable-curve: the existing definition only defines strict semistability; this node gives an iff criterion for ordinary semistability after contraction.

lem-trf-valuation-nodal-polar-section vs def-trf-modification: the existing definition only defines a modification; this node constructs horizontal Cartier divisors and a lifted polar section on a normal proper curve.

lem-trf-valuation-nodal-polar-section vs def-trf-multipointed-curve-modification: the existing definition only defines multipointed modifications; this node constructs divisors and sections on the underlying proper curve.

lem-trf-valuation-nodal-polar-section vs def-trf-rational-rank: the existing definition concerns valuation rank; this node concerns divisors and sections on a nodal fibre.

lem-trf-valuation-nodal-polar-section vs def-trf-schematically-dense-open: the existing definition only defines schematic density; this node constructs a polar linear system.

lem-trf-valuation-nodal-polar-section vs def-trf-strict-semistable-curve: the existing definition only defines strict semistability; this node constructs sections with prescribed poles and makes no strictness assertion.

lem-trf-valuation-nodal-polar-section vs def-trf-strictly-semistable-curve: the existing definition only defines strict semistability; this node constructs sections with prescribed poles and makes no strictness assertion.

lem-trf-valuation-normalized-graph-model vs def-trf-modification: the existing definition only defines a modification; this node constructs the normalized graph model and its connected-fibre and contraction properties.

lem-trf-valuation-normalized-graph-model vs def-trf-multipointed-curve-modification: the existing definition only defines multipointed modifications; this node concerns normalized graph images of curve morphisms.

lem-trf-valuation-normalized-graph-model vs def-trf-rational-rank: the existing definition concerns valuation rank; this node concerns graph normalization and fibre contractions.

lem-trf-valuation-normalized-graph-model vs def-trf-schematically-dense-open: the existing definition only defines schematic density; this node proves a normalized graph factorization theorem.

lem-trf-valuation-normalized-graph-model vs def-trf-strict-semistable-curve: the existing definition only defines strict semistability; this node proves a graph normalization theorem for normal curves.

lem-trf-valuation-normalized-graph-model vs def-trf-strictly-semistable-curve: the existing definition only defines strict semistability; this node proves a graph normalization theorem for normal curves.

lem-trf-valuation-curve-projective-preparation vs def-trf-semistable-multipointed-pair: the existing definition only defines semistability and geometric stability of an underlying pair; the new statement proves finite normalization, a normal projective preparation, and locality/gluing over a valuation curve.

lem-trf-valuation-curve-projective-preparation vs lem-trf-base-modification-comparison-fibre-image: the existing lemma compares fibre images after a proper birational Noetherian base change and proves finiteness of a closed-point image; the new statement treats finite-height valuation curves and constructs normalization, compactification, and local gluing.

lem-trf-valuation-exceptional-local-criterion vs def-trf-semistable-multipointed-pair: the existing definition only defines semistability and stability of a pair; the new statement gives openness and an iff exceptional-tree criterion for a contraction fibre.

lem-trf-valuation-exceptional-local-criterion vs lem-trf-base-modification-comparison-fibre-image: the existing lemma concerns finite images of fibres under a Noetherian base comparison and has no semistability criterion; the new statement characterizes semistability at a contraction by the exceptional reduced fibre tree.

lem-trf-valuation-nodal-polar-section vs def-trf-semistable-multipointed-pair: the existing definition only defines a semistable pair; the new statement constructs horizontal Cartier divisors and a section with prescribed poles on the nonexceptional fibre components.

lem-trf-valuation-nodal-polar-section vs lem-trf-base-modification-comparison-fibre-image: the existing lemma proves finiteness of a fibre image after Noetherian base change; the new statement constructs a polar linear system on a normal proper valuation curve and makes no fibre-image comparison.

lem-trf-valuation-normalized-graph-model vs def-trf-semistable-multipointed-pair: the existing definition only defines semistability and stability of an underlying pair; the new statement constructs a normalized graph intermediate model and describes its connected fibres and contractions.

lem-trf-valuation-normalized-graph-model vs lem-trf-base-modification-comparison-fibre-image: the existing lemma gives a finite closed-point fibre image under a Noetherian base comparison; the new statement normalizes a relative graph image over a valuation curve and proves factorization, connectedness, and contraction properties.

lem-trf-valuation-exceptional-local-criterion vs def-trf-birational-quasi-modification: the existing node only defines separated finite-type birational quasi-modifications; this input states the distinct semistability locus and exceptional-tree local criterion.

lem-trf-valuation-exceptional-local-criterion vs def-trf-centred-valuation: the existing node only defines a centred valuation morphism Spec V to a scheme, and states none of this relative-curve theorem.

lem-trf-valuation-exceptional-local-criterion vs def-trf-nodal-dualizing-datum: the existing node defines a complete-intersection dualizing datum and its Jacobian normalization, and states none of this relative-curve theorem.

lem-trf-valuation-nodal-polar-section vs def-trf-birational-quasi-modification: the existing node only defines separated finite-type birational quasi-modifications; this input states the distinct polar divisor and section existence theorem.

lem-trf-valuation-nodal-polar-section vs def-trf-centred-valuation: the existing node only defines a centred valuation morphism Spec V to a scheme, and states none of this relative-curve theorem.

lem-trf-valuation-nodal-polar-section vs def-trf-nodal-dualizing-datum: the existing node defines a complete-intersection dualizing datum and its Jacobian normalization, and states none of this relative-curve theorem.

lem-trf-valuation-curve-projective-preparation vs def-trf-birational-quasi-modification: the existing node only defines separated finite-type birational quasi-modifications; this input states the distinct normalization/compactification/locality theorem.

lem-trf-valuation-curve-projective-preparation vs def-trf-centred-valuation: the existing node only defines a centred valuation morphism Spec V to a scheme, and states none of this relative-curve theorem.

lem-trf-valuation-curve-projective-preparation vs def-trf-nodal-dualizing-datum: the existing node defines a complete-intersection dualizing datum and its Jacobian normalization, and states none of this relative-curve theorem.

lem-trf-valuation-normalized-graph-model vs def-trf-birational-quasi-modification: the existing node only defines separated finite-type birational quasi-modifications; this input states the distinct normalized graph factorization and connected-fibre theorem.

lem-trf-valuation-normalized-graph-model vs def-trf-centred-valuation: the existing node only defines a centred valuation morphism Spec V to a scheme, and states none of this relative-curve theorem.

lem-trf-valuation-normalized-graph-model vs def-trf-nodal-dualizing-datum: the existing node defines a complete-intersection dualizing datum and its Jacobian normalization, and states none of this relative-curve theorem.

## Unfinished work

No parent proof clause remains open. Required server dry-run and push follow this report. No Lean was written and no compiler, Lake or build tool was run.

