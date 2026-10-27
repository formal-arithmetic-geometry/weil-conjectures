## Worker report

Files written (all under the dispatched sandbox):

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-single-complex-base-change.json`: item, split; statement unchanged; five-step assembly proof.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-stalk-condition-etale-charts.json`: statement, unsplit; Mathlib searches found no match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-qcqs-distinguished-square-induction.json`: statement, unsplit; Mathlib searches found no match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-mv-exchange-triangles.json`: statement, unsplit; Mathlib searches found no match.
- `citations.json`: fourteen verbatim statement citations, one for each use in each proof step.
- `searches.jsonl` and `research/*-searches.json`: actual search log and full returned results. The helper script and raw evidence stay in the sandbox, outside the delivery node files.

Attachments: none. Searched the live `lean/WeilConjectures/` for the exact blueprint tag, single-complex terminology, algebraic spaces, 0DKG/0DKH/08GP/08JK, and distinguished-square induction. No exact project declaration was found. Existing scheme or constant-coefficient results do not attach to this structure-sheaf algebraic-space statement.

WANTED: none. All mathematical sources used were read in the local Stacks source.

The original item had an empty proof. Its statement agrees with spaces-perfect.tex Tag 0DKH, using condition (1) and equation-bc of 0DKG; no statement correction was needed. Its stalks are geometric, whereas the existing scheme criterion uses ordinary Zariski stalks. The chart-condition node makes that transition explicit instead of applying the scheme criterion directly to geometric stalks. The existing space flat-direct-image node is only underived degree zero, requires separatedness, and cannot justify the localization here; the existing derived etale chart calculus supplies the needed unbounded restriction comparisons instead.

The current latest blueprint unit and direct-images proof (3) were read. The item is an inherited supporting input below this route, not the unit's key statement; no unit or chapter record was changed. `blueprint_refs.py ancestor` currently reports `None`; the inherited null ancestor and via chain were preserved, with the item prepended on the new nodes. The existing from.place identifies the direct-image supporting route precisely. This records the current imported metadata rather than inventing a blueprint id.

Nothing remains unfinished in this one-level split. The three new nodes intentionally have statements only, no proof steps or proof dependencies. They remain stage-1 work items. No Lean was written and no compiler, Lake or build tool was run. No repository or launcher file was written.

## Searches and source checks

Before creating the nodes I searched the whole DAG by source labels, tags 08GP, 08JK, 0DKG, and the key phrases elementary distinguished square, etale restriction, single-complex base change, and algebraic-space induction. I also ran `tools/blueprint_refs.py search` for 08GP, 08JK, 0DKG, single complex base change, single-complex, distinguished square, Mayer Vietoris, and etale restriction. The only blueprint hit relevant to restriction concerned constant-ring etale sheaves; it does not state the structure-module theorem here. Read existing scheme criterion and relative Mayer–Vietoris nodes, etale–Zariski comparison nodes, space chart calculus, geometric-stalk tensor calculus, and flat-direct-image node before deciding what was missing.

Each of the three new nodes and the item has actual LeanFinder searches with two distinct phrasings, LeanSearch, Loogle and grep searches through the mandated msearch.py command. Full returned types are retained in the node records. All services returned successfully. The induction hits include AlgebraicGeometry.compact_open_induction_on: its type concerns open subsets of one scheme and adjoining affine opens, not etale algebraic spaces or elementary distinguished squares. Read its local declaration at Morphisms/QuasiCompact.lean:241. For Mayer–Vietoris, read Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean:15 onward: it gives the long exact cohomology sequence of one abelian sheaf, not the unbounded relative structure-module triangle or compatibility of the specified exchange maps with its connecting arrow. The stalk hits concern scheme ring-hom properties, flat stalk maps, or rank of ordinary tensor products, and do not compare the two derived stalk conditions. Consequently none is an exact match or a one-line specialization.

## Not duplicates

lem-sfb-space-stalk-condition-etale-charts vs lem-sfb-space-single-complex-base-change: the new node compares geometric and ordinary chart stalk hypotheses; it asserts no direct-image isomorphism.

lem-sfb-space-stalk-condition-etale-charts vs lem-sfb-space-single-complex-tensor-inheritance: inheritance tensors a coefficient map with an arbitrary complex; the new node instead changes from geometric stalks to etale scheme charts and ordinary Zariski stalks.

lem-sfb-space-stalk-condition-etale-charts vs lem-sfb-space-geometric-stalk-tensor-calculus: the latter identifies pullback stalks and flatness of the tensor-to-fibre stalk ring; it does not equate the geometric condition with ordinary stalk tests on chart diagrams.

lem-sfb-space-stalk-condition-etale-charts vs lem-sfb-space-flat-complex-base-change: the latter is a direct-image theorem for tensoring with a bounded-above relatively flat complex, not the chart criterion of 0DKG.

lem-sfb-space-relative-mv-exchange-triangles vs lem-sfb-space-single-complex-base-change: the new node is the generic morphism of Mayer–Vietoris triangles before imposing any invertibility assumptions; it does not conclude that any exchange component is invertible.

lem-sfb-space-relative-mv-exchange-triangles vs lem-sfb-space-flat-complex-base-change: the latter has relative flatness and a direct-image isomorphism conclusion, and supplies neither relative elementary-distinguished-square triangles nor the connecting-arrow compatibility.

lem-sfb-space-relative-mv-exchange-triangles vs lem-sfb-space-single-complex-tensor-inheritance: that tensor-stalk inheritance result does not concern relative Mayer–Vietoris triangles.

lem-sfb-space-relative-mv-exchange-triangles vs lem-sfb-space-geometric-stalk-tensor-calculus: that stalk calculation has no relative triangles or boundary maps.

lem-sfb-space-relative-mv-exchange-triangles vs lem-pc-rf-single-complex-relative-mayer-vietoris: the existing node concerns two quasi-compact open subschemes of a scheme and concludes invertibility from three invertibility assumptions. The new node concerns an open plus an etale neighbourhood in algebraic spaces and gives the actual triangle morphism, including its boundary, without invertibility assumptions.

lem-sfb-space-qcqs-distinguished-square-induction vs lem-sc-invert-s-cohomology-induction: the existing induction concerns quasi-compact opens in a scheme; the new statement permits nonschematic etale algebraic spaces and the elementary distinguished squares of 08GP.

lem-sfb-space-relative-mv-exchange-triangles vs def-pd-section-derived-realization: the existing node defines normalization of derived section-module operations for condensed coefficients on pro-etale schemes; it does not assert a relative Mayer–Vietoris triangle or its exchange boundary square.

lem-sfb-space-relative-mv-exchange-triangles vs def-pd-section-derived-tensor-data: the existing node packages conjugate derived tensors and section equivalences for condensed pro-etale coefficients, without relative distinguished-square triangles.

lem-sfb-space-relative-mv-exchange-triangles vs lem-pd-module-ringed-topos-derived-comparison: the existing node compares internal condensed module objects with ringed-topos derived operations on pro-etale schemes, including tensor maps; it does not give the relative elementary-distinguished-square triangle morphism on algebraic spaces.

lem-sfb-space-relative-mv-exchange-triangles vs lem-pd-section-derived-pushpull-normalization: the existing node identifies adjunctions under the pro-etale section-module equivalence, rather than asserting relative Mayer–Vietoris or connecting-map compatibility under base change.

lem-sfb-space-relative-mv-exchange-triangles vs def-pbc-successive-derived-scalar-normalization-data: the existing node defines data for successive ring-sheaf scalar extensions and their normalized adjunctions; it asserts neither existence nor any relative algebraic-space Mayer–Vietoris triangle.

lem-sfb-space-relative-mv-exchange-triangles vs def-weil-pbc-derived-direct-image-composition: the existing node defines composition isomorphisms on bounded-below abelian etale derived categories of schemes; it is not the unbounded structure-module elementary-distinguished-square comparison.

lem-sfb-space-relative-mv-exchange-triangles vs def-weil-pbc-derived-normalization-arrows: the existing node defines constant-sheaf and coefficient-restriction normalization maps, without relative Mayer–Vietoris triangles or their exchange maps.

lem-sfb-space-relative-mv-exchange-triangles vs def-weil-pbc-ringed-slice-derived-data: the existing node packages derived functors and slice comparison equations as data, and does not prove a relative Mayer–Vietoris triangle morphism.

lem-sfb-space-relative-mv-exchange-triangles vs def-weil-pbc-successive-derived-quotient-data: the existing node defines presentations and normalization data for coefficient ring changes; it contains no relative distinguished-square or boundary compatibility theorem.

lem-sfb-space-relative-mv-exchange-triangles vs lem-pbc-normalized-derived-adjunction-transport: the existing node transports a universal derived pair and its normalized adjunction across additive equivalences; it does not construct relative Mayer–Vietoris triangles or compare their canonical boundary maps.

lem-sfb-space-relative-mv-exchange-triangles vs lem-weil-pbc-cohomology-pullback-derived-unit: the existing node identifies Leray and pullback maps on bounded-below abelian etale cohomology of schemes; it gives no relative algebraic-space structure-module triangle or connecting square.

## Review by Q75

I read spaces-perfect.tex, equation-bc, Tag 0DKG (lemma-single-complex-base-change-condition), and the entire statement and proof of Tag 0DKH (lemma-single-complex-base-change). The item matches the Cartesian square, unbounded D_QCoh coefficients, arbitrary coefficient map, qcqs hypothesis on f, and the precise composite in that source. The cohomology tensor in its assumption is an ordinary tensor over A tensor_R B, not an assertion that the original square is Tor-independent. Properness, boundedness and flatness have not been introduced.

For the chart-condition node I read the proof of 0DKG, including the displayed ordinary/geometric-stalk square, faithful flatness of strict henselization, and the use of more-algebra-lemma-lemma-tor-independent-flat-compare. Its conclusion is a condition equivalence, so no per-degree substitute is being used for a derived-object identification. I checked the diagram requires all three chart maps a,b,c to be etale, and U'=U times_V V'. With schemes representing all four spaces, the condition is exactly that of the existing ordinary-stalk node. The additional etale restrictions use unchanged geometric stalks and their natural scalar-extension maps. The statement does not claim arbitrary non-etale base change preserves the condition.

For the induction node I read Tag 08GP (lemma-induction-principle) in full. The property is on qcqs etale algebraic spaces over X, not merely on affine charts. The two premises are affine objects and the precise elementary distinguished-square gluing premise with U quasi-compact and V affine. Its domain includes the intersection and X itself. The empty affine is allowed, so no unstated nonemptiness assumption enters. The general induction is a real supporting result, not a clause of the direct-image theorem.

For the triangle node I read Tag 08JK (lemma-unbounded-relative-mayer-vietoris), including its construction from a short exact sequence of termwise injective K-injective resolutions, and the full induction-step diagram in 0DKH. This is one compatibility result: the relative triangles and their base-change morphism with the specified components. The assertion expressly includes the connecting square; an arbitrary completion by TR3 would not suffice. The source gives arbitrary unbounded objects and does not impose qcqs or relative flatness to construct the triangles. Its maps are the canonical counit mates from sites-cohomology.tex Tags 07A6 and 07A7. I repaired the inline definition of elementary distinguished square to use the actual variables X,U,V consistently, so no auxiliary W is left undeclared.

Step 1 uses the statement of lem-sfb-space-derived-etale-chart-calculus for exact etale restriction, both derived restriction comparisons, and compatibility of composition with units and counits. It uses the atlas clause of def-trf-algebraic-space and the covering clause of lem-trf-space-fibre-products-etale-covers to obtain the successive affine charts. The new condition node supplies preservation of the hypothesis. Vanishing of a sheaf on a covering implies zero directly by the sheaf axiom, so no constant-coefficient geometric-point theorem is being used. Quasi-compactness and quasi-separatedness of the restricted f are just the chart-tested hypothesis of the item; over an affine base its source is qcqs.

Step 2 defines P on exactly the domain required by the new induction node. It does not assume the result for every etale object. Restrictions and the pullback composition comparison come from the chart calculus; the new chart-condition node supplies the hypothesis on every restriction. No direct-image preservation theorem is implicitly needed to define P: its arrows exist in the ambient unbounded derived categories.

Step 3 uses the full statement of lem-sfb-derived-etale-zariski-equivalence, including pullback comparisons for every morphism and direct-image comparison for qcqs morphisms. The ordinary scheme theorem lem-pc-rf-single-complex-qcqs-induction says exactly that the composite is invertible under the ordinary stalk condition; I read its full statement, not its proof. The chart-condition node supplies precisely that hypothesis. For this affine premise, T,Y,Y' are affine schemes, their fibre product T' is a scheme, and a morphism of affines is qcqs, so the scheme theorem's hypotheses hold. The canonical comparisons transport the actual adjunction-mate arrow rather than merely identifying its source and target objects.

Step 4 takes the distinguished rows and all three specified components, including the boundary compatibility, from the new triangle statement. It applies the existing lem-sf-triangle-morphism-iso only after this morphism is present. That node states two-out-of-three for the components of a morphism of distinguished triangles, which is precisely the situation. The direct-sum inverse is the direct sum of the given inverses, an elementary identity. This step has no assertion that the etale neighbourhood V is an open subspace, or that the intersection is affine; neither is required.

Step 5 uses the actual conclusion of 08GP as stated in the new induction node and the unital restriction comparisons of the chart calculus. At T=X the construction is the item's canonical composite. The final covering argument uses exact restriction and sheaf vanishing, not a new base-change theorem.

I checked B1–B10 and C1–C8 with the node statements open: all new nodes are self-contained statement-only records, notions are defined inline or cited through genuine definitions, sources carry tags and labels, search strings and returned results are genuine, and the same-source-tag near matches are distinguished above. New nodes introduce neither a disguised restatement of the item nor an elementary corollary already available from another node. For D1–D5 the proof stays in the item: it assembles scheme comparison and induction; the supporting triangle node has no invertibility conclusion. For E1–E7 I checked the chart hypotheses, ordinary versus geometric stalk rings, unboundedness, and the actual mate and boundary arrows. Small cases were the identity base change, K=K'=0, empty X or Y', the degenerate square U=W, and U empty with V=W. All statements reduce to the identity or zero triangle as expected. No hypothesis is dropped in these cases. No proof step exceeds 2000 characters (the longest is 707); the whole assembly has 2532 characters. No further hidden sublemma was retained in a long step.

The generic scheme criterion and triangle two-out-of-three lemma are declared as tool uses in split_report. They are the precise tools explicitly used by 0DKH, rather than a replacement of the unit route. The server check_dag run passed before the final report. The required dry run and delivery follow this review.

The first dry run stopped at the same-tag duplicate gate for eleven 07A6 nodes. I opened and read all eleven statements and added the explicit comparisons above; none states the Mayer–Vietoris compatibility assertion. The node source tags were retained unchanged.
