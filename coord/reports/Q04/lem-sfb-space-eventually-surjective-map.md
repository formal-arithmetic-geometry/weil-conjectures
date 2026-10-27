## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-eventually-surjective-map.json: split the item into four steps, with no statement change.
- citations.json: ten citations, each quoting the cited statement verbatim.
- searches.jsonl: five actual Mathlib searches for this item, supplementing the inherited records.

New nodes: 0. Mathlib leaves: 0. No Lean written and no compiler invoked.

## Attachments

None. The project search by the item tag and by eventual surjectivity found no declaration for algebraic spaces. AlgebraicGeometry.exists_surjective_of_isLimit in lean/WeilConjectures/AlgebraicGeometry/DescendSurjective.lean states the scheme input, already attached to lem-weil-pbc-descend-surjective; it does not state this item for algebraic spaces.

## WANTED

None.

## Corrections and unfinished work

The imported statement is faithful to Stacks 07SN in Situation 084W, with persistence under base change, and stays unchanged. Its empty proof is replaced by the chart argument. I made explicit the base system for the scheme theorem: S_i = V_i. The original B_i can be algebraic spaces, so applying a scheme theorem directly over them would be invalid. Since U_i = U_0 times_{V_0} V_i, the scheme theorem applies over V_i and gives exactly the desired chart morphism. There is no remaining gap in this one-level split. The inherited null blueprint ancestor is retained: blueprint_refs.py ancestor reports None for the item's creation chain. I read the latest chapter/unit and direct-images proof (3); this is the inherited supporting approximation route, not a replacement of the unit argument.

## Not duplicates

No new nodes. DAG tag searches for 07SN and lemma-descend-surjective distinguish the item from the existing scheme result 07RR, which is reused. blueprint_refs.py searches for 07SN and descend-surjective each returned zero blueprint matches. The broader surjective search and latest-blueprint text search supplied no exact algebraic-space duplicate. Existing atlas, qcqs-product, chart-property, affine-limit, affine-locality and point-calculus statements are reused.

## Mathlib searches

Read all five msearch.py outputs, including the second semantic phrasing. Loogle returned zero; grep returned scheme flat-descent declarations. The semantic hits concern fpqc descent of scheme properties, ordinary scheme surjectivity, light profinite transitions, or eventual equality of maps from scheme limits. I read FlatDescent.lean:160-185, UnderlyingMap.lean:50-64 and AffineTransitionLimit.lean:1040-1061. Their objects and conclusions do not give 07SN for algebraic spaces. Every added mathlib_searches record has exactly the tool and query recorded by the command. No service failure was recorded as absence.

## Review by Q04

I read Stacks spaces-limits.tex Tag 07SN in full, its Situation 084W, and the scheme input limits.tex Tag 07RR and its proof. I also read the supporting source statements: spaces-properties.tex 03H6 (affine etale atlas), 03H4/03H5 (points and surjectivity); spaces-morphisms.tex 073B(3), 03WG/03WI and 0410 (qcqs products, affineness and local finite presentation on charts); and spaces-limits.tex 07SF (existence of affine-transition limits, affine projections, and base-change compatibility). No SGA source is used.

Step 1 uses the statement of lem-sfb-qc-space-affine-etale-atlas, which requires topological quasi-compactness and gives one affine surjective etale chart. That hypothesis holds first for Y_0, then for W_0. I checked lem-weil-pbc-affine-scheme-qcqs for V_0 and lem-sfb-qcqs-space-fibre-product with all three inputs X_0, Y_0, V_0 qcqs, including the base Y_0; thus W_0 is qcqs. The statement of lem-sfb-space-local-properties-chart-test explicitly allows exactly the two charts V_0 to Y_0 and U_0 to X_0 times_{Y_0} V_0 and concludes that U_0 to V_0 is locally of finite presentation. No composition theorem or hidden stronger hypothesis is used.

Step 2 uses only the stated limit projection/base-change clauses of lem-sfb-space-affine-limits-schematic-stages, not its proof or its eventual-scheme conclusion. The statement of lem-sfb-space-affine-locality supplies base-change stability and the affine source over an affine target, so U_i,V_i,U,V are schemes and affine. Both transition systems are base changes of the B transition system. The sheaf universal property restricts to scheme tests and gives the required scheme limit. Pullback associativity gives U_i = U_0 times_{V_0} V_i; it is an identity of the two specified pullback diagrams, not an identification merely from equality of images. The explicit covering base-change clause of lem-trf-space-fibre-products-etale-covers gives both surjective etale maps at every stage and at the limit.

Step 3 uses the full point-image formula in lem-a1-space-point-open-calculus, not just the definition of surjectivity. It gives the surjectivity of the pullback of f, and composition with the atlas gives surjectivity of h. I opened lem-weil-pbc-descend-surjective and checked its statement: it allows any directed scheme base system with affine transitions, needs qcqs at the chosen stage and lfp of h_0, and produces one later surjective map. Set its base system equal to V_i, stage source U_0 and target V_0. Affineness supplies all qcqs assumptions, and step 1 supplies lfp. The point classes of schemes are their underlying scheme points, as in the point-space conventions. Thus its surjectivity hypothesis and conclusion are the ones being used.

Step 4 spells out the two preimages from the surjective chart and h_j, then uses commutativity to obtain a preimage in X_j for every point of Y_j. For i beyond j, pullback associativity identifies f_i with the base change of f_j, and the quoted point-image formula gives all later surjectivities. This step is elementary relative to that explicit cited formula. No surjectivity of B_i to B_j or of a limit projection is assumed.

I checked delivery-errors B through E against these statements and sources: no new lemma restates the item, no unsplit node contains a proof, no unrecorded literature lemma hides in a step, and every uses entry has a verbatim statement quotation. The generic off-unit inputs are declared in split_report.tool_uses. I checked the dependency graph for paths from the proposed inputs back to this item and found none. The local step lengths are below 2000 characters. Small cases: empty Y_0 and empty atlases (Spec 0); a constant system and singleton index; empty limit with nonempty early stages; and nonsurjective transition maps. The scheme 07RR input permits these cases and no step chooses a point of an empty space. In particular if the limit target is empty the chart limit is empty and 07RR still supplies the eventual surjectivity stage; no projection-surjectivity shortcut is used.

The preliminary server review_split check passed with zero new nodes. The required complete dry run is run after writing this report.
