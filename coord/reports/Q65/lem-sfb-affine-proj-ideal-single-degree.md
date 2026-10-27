# Worker report: lem-sfb-affine-proj-ideal-single-degree

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-affine-proj-ideal-single-degree.json: item, statement unchanged, split into six steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-proj-map-standard-charts.json: statement, Mathlib leaf. General graded Proj morphism with irrelevant-ideal containment, standard-open inverse images and chart fraction formula. Its proof and proof_deps are empty.
- citations.json: twelve verbatim statement excerpts, covering every proof-step citation.

## Attachments

None. Searched lean/WeilConjectures for the item's blueprint tag, single-degree terminology, homogeneous ideals, quotient/Proj and graded map terminology. No finished project declaration states the item. Mathlib declarations are recorded as a leaf, not a project attachment.

## Wanted literature

None. Read the existing local Stacks sources.

## Problems found and changes

No statement dispute. The input permits arbitrary R → A_0 and makes no finite generation assumption on A, I, or any homogeneous piece. These hypotheses are retained. The broader scheme recovery result is unnecessary: I is already an input. No dependency on the item's parent was introduced.

Stacks divisors.tex, Tag 0802, label lemma-closed-subscheme-proj-finite, supplies the affine argument. Its text chooses d as a common multiple of degrees; to justify all exponents explicitly, step 4 uses L = product of the positive chart degrees and d = L(E+1), where E bounds the numerator exponents. This ensures d/a_i ≥ e_ij as well as divisibility. The global extension lemma in the source is unnecessary over the single affine base: F is the actual finite R-span of the constructed elements.

The degree-one quotient-chart-kernel node does not apply to arbitrary positive chart degrees. I did not cite it outside its hypotheses or create a generalization containing the item's argument. Instead step 2 proves the elementary kernel calculation using the localization equivalence relation. The non-elementary chart morphism formula is already Mathlib and is the one new leaf.

The inherited blueprint ancestry returns None. Retained its null ancestor and via chain, with an explicit place identifying the 0802 affine reduction and the current blueprint det-thm-sf-ctf-stability-direct-images proof (3), compactification. Read the current literature/blueprint/latest version and the item's unit/chapter; the split is below their inherited Chow-modification prerequisite and does not replace any unit step.

## Unfinished work

None within this one-level stage-1 split. No Lean files, compilers or build tools were used.

## Not duplicates

lem-sfb-proj-map-standard-charts vs lem-nagata-affine-proj-scalar-extension: the existing node assumes a tensor scalar-extension presentation and proves a cartesian square; the new leaf treats arbitrary graded maps satisfying irrelevant-ideal containment and asserts only the morphism and chart formulas.
lem-sfb-proj-map-standard-charts vs lem-trf-local-proj-isomorphism-compatibility: the existing node treats graded sheaf algebra isomorphisms, restrictions and degreewise units; the leaf allows noninvertible graded ring maps.
lem-sfb-proj-map-standard-charts vs def-sfb-relative-proj-iso-of-graded-iso: the existing definition specifies relative Proj isomorphisms of sheaf algebras; the leaf states the chart theorem for arbitrary noninvertible graded ring maps satisfying the irrelevant containment.
lem-sfb-proj-map-standard-charts vs lem-sfb-proper-ample-section-proj-reconstruction: the existing node reconstructs a proper polarized scheme from its section ring; the new leaf assumes no line bundle, proper scheme, or section-ring presentation.
lem-sfb-proj-map-standard-charts vs lem-sfb-homogeneous-quotient-chart-kernel: the existing node assumes a homogeneous quotient and a degree-one denominator and identifies its kernel; the new leaf allows arbitrary graded maps and positive degrees and asserts no kernel calculation.
lem-sfb-proj-map-standard-charts vs lem-per-finite-graded-proj-morphism: the existing theorem assumes an injective finite graded extension and finite-type algebra and concludes finite surjectivity; the leaf has only irrelevant-ideal containment and concludes neither property.
lem-sfb-proj-map-standard-charts vs lem-sfb-graded-proj-quotient-twist-comparison: the existing theorem assumes an algebra generated in degree one and a surjection and proves twist isomorphisms; the new leaf has neither assumption and asserts only the general map and chart formula.
lem-sfb-proj-map-standard-charts vs prop-nagata-relative-proj-functoriality: the existing statement gives closed immersions for surjections and isomorphisms for equivalences, but does not state standard-open inverse images or the chart ring map and does not cover general graded ring maps under irrelevant containment.

## Review by Q65

I read divisors.tex at Tag 0802 (lemma-closed-subscheme-proj-finite), morphisms.tex at Tag 01TV (lemma-closed-immersion-finite-presentation), properties.tex at Tag 01PB (lemma-finite-type-module), and constructions.tex at Tag 01MY (lemma-morphism-proj, clause (2)). The item is precisely the affine construction inside 0802 with a homogeneous ideal already supplied. The single new node states the general map formula of 01MY in the everywhere-defined case. I checked its exact Mathlib sources in ProjectiveSpectrum/Functor.lean: variables at 92–96, map at 148, map_preimage_basicOpen at 160, awayι_comp_map at 192, and HomogeneousLocalization.lean Away.map_mk at 730. Thus it is a Mathlib leaf, not another queued unsplit lemma. Each recorded query was run through msearch.py; searches.jsonl retains the exact results. Loogle and grep locate the actual leaf; semantic hits alone were not treated as matches. Read the candidate finite-generation theorems too: HomogeneousLocalization.Away.span_mk_prod_pow_eq_top requires algebra generators, and Away.finiteType requires finite type of the whole algebra, so neither proves the item.

Step 1: opened lem-weil-pbc-proj-standard-open-inclusion, which explicitly states that positive homogeneous standard opens form a basis. Compactness supplies the finite subcover. Opened def-sbc-closed-immersion-ideal-sheaf, whose statement explicitly gives the kernel on all opens and its quasi-coherence, and lem-trf-closed-immersion-finite-presentation-ideal, whose finite-presentation iff finite-type-ideal criterion applies to any scheme. The item supplies exactly that finite presentation; no Noetherianity or finite generation of A is smuggled in.

Step 2: the new leaf supplies both the inverse-image chart and the fraction map, which the old generic Proj functoriality node alone did not state. For the quotient grading, every homogeneous element lifts in the same degree, so irrelevant containment holds. Opened both degree-zero homogeneous localization and ordinary localization definitions; their explicit fraction and equality descriptions justify surjectivity and the f^k b kernel calculation. This step proves the kernel formula itself and makes no unsupported identification of reduced supports with closed subschemes. Nilpotence is allowed: the zero localization obeys the same formula.

Step 3: opened lem-weil-pbc-quasi-coherent-finite-type-affine. Its clause (a) concerns every affine open of every scheme, despite its proper-base-change unit. It gives finite generators of J(D_+(f_i)) because step 1 proves J is quasi-coherent of finite type and def-pc-proj makes those charts affine. The kernel calculation gives numerators inside I. Multiplying a numerator and denominator by f_i makes its exponent positive without altering the fraction. No lift out of the given ideal is assumed.

Step 4: elementary finite arithmetic and the ideal axioms give d > 0, divisibility, nonnegative exponents, and g_ij in I_d. I checked the product formula works even when a chart's generating list is empty. Multiplication of R scalars stays in degree d because R → A_0. The generated A-ideal is homogeneous by componentwise expansion, so the quotient construction in the statement applies.

Step 5: elementary ideal inclusions and the displayed fraction identity prove equality of chart kernels. Generators from other charts belong to I and therefore cannot enlarge the ideal beyond the desired kernel. This is equality of ideals, without taking radicals or asserting equality of the underlying homogeneous ideals.

Step 6: opened prop-nagata-relative-proj-functoriality and used only its explicitly stated closed-immersion clause. Opened def-weil-closed-immersion for its affine quotient description and def-sbc-closed-immersion-ideal-sheaf for the actual associated ideal sheaf on affine opens. Equal chart kernels give equal ideal subsheaves on the cover, hence equal closed subschemes with their quotient structure sheaves. This corrects the risk of proving only equal topological vanishing loci.

The generic uses of the off-unit finite-presentation-ideal and affine finite-type-module criteria are declared in split_report.tool_uses; they serve the existing 0802 route. No tool_uses acceptance field was written. I searched the whole DAG by 0802, 01MY, relevant declaration names, homogeneous quotient and Proj chart terms, and ran blueprint_refs.py searches for Proj, morphism-proj, homogeneous quotient, standard open and irrelevant. The existing same-tag nodes differ as recorded above. No new node is a clause of the item, no elementary fact became a node, and the new leaf carries no proof sketch.

Small cases checked against the written argument: empty Proj (d=1, empty list); I=0 and I with zero associated ideal (empty local lists); I=A (unit chart ideals can be represented by f_i/f_i); zero ring; nilpotent f_i and empty charts; A concentrated in degree zero; all positive degrees divisible by 2 rather than generated in degree one; degree-zero elements of I; arbitrary non-surjective R → A_0. None requires an extra hypothesis. No non-elementary step is longer than 2000 characters. The twelve citation excerpts are verbatim substrings of the nodes' current statements. The first full dry run required a dedicated mathlib_match.line field even though the lines were already documented in how; I added line 148 after checking the source above.

Mechanical review_split ran on the server and passed. Full dry-run and delivery results are recorded by the delivery tool.
