# lem-trf-ample-neighbourhood — NU

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-ample-neighbourhood.json`: seven-step split of Stacks 0D2S; statement and statement dependencies retained exactly.
- `dag/nodes/sec-trace-formula/lem-trf-invertible-affine-limit-descent.json`: statement, unsplit, no Mathlib match; Stacks 0B8W(2).
- `dag/nodes/sec-trace-formula/lem-trf-ample-affine-limit-descent.json`: statement, unsplit, no Mathlib match; Stacks 09MT.
- `dag/nodes/sec-trace-formula/lem-trf-noetherian-fibre-ample-neighbourhood.json`: statement, unsplit, no Mathlib match; Stacks 0D2N, with an affine neighbourhood chosen inside its conclusion.
- `citations.json`: 28 verbatim statement quotations, one for every use in the seven steps.
- `searches.jsonl` and `search-results.jsonl`: executed queries and their actual outputs. The helper scripts and these research records stay in this sandbox.

## New nodes

`lem-trf-invertible-affine-limit-descent` supplies finite-stage descent of the line bundle, independently of properness or ampleness. It is exactly clause (2) of Limits `lemma-descend-invertible-modules`, tag 0B8W, read at lines 2607 onward in `literature/stacks-project/limits.tex`.

`lem-trf-ample-affine-limit-descent` supplies finite-stage detection of ampleness for a line bundle already at a stage. I read Limits `lemma-limit-ample`, tag 09MT, lines 787–806, and its full qcqs/affine-transition situation 01YX at lines 387–403. Its statement retains those assumptions and the fixed initial stage. The source proof's first displayed sentence suppresses the positive tensor powers of sections; the ampleness definition and the node statement retain those powers. No source theorem has been altered.

`lem-trf-noetherian-fibre-ample-neighbourhood` isolates the genuinely Noetherian cohomological theorem 0D2N, `lemma-ample-in-neighbourhood` in `literature/stacks-project/coherent.tex`, lines 6090–6164. I read its entire statement and proof, including the choice of liftable sections and the finite-morphism argument at the end. Its conclusion follows by choosing an affine open containing the point within the relative-ampleness neighbourhood. This is a substantive reduction of 0D2S to the Noetherian case, not a replacement name for the original general-base theorem: the item itself carries the approximation, line-bundle descent, fibre-limit comparison, descent of fibre ampleness, and pullback argument. The three children have no proofs or proof dependencies.

## Attachments

None. Searched `WeilConjectures/` in slopmaster2 for the item id, the blueprint tag, ampleness/neighbourhood terms, the source tags 0B8W/09MT/0D2N, and descent/limit terms. Read relevant declarations/search results from `AlgebraicGeometry/Modules/Ample.lean` and searched the limit source. The project has field-base very-ampleness descent and other ampleness facts, but no declaration stating any of these four items exactly. Upstream master was used only as reference, never as proof evidence.

## WANTED

None. All proof sources needed here are in the local Stacks checkout.

## Corrections and route

No statement dispute. The original statement is true with its arbitrary base and extra quasi-compactness conclusion. No hypotheses, dimensions, connectedness, reducedness, flatness, or finite-presentation assumptions were added. The item was unsplit and had no proof. Its statement, dependencies and historical ancestry are retained.

I read the chapter and unit, the current main-20261015 ancestor text, and the existing parent `lem-trf-proper-fibrewise-ample-projective`. This is the auxiliary 0D2S input on that parent's fibrewise ampleness-to-projectivity route below `lem-trf-local-term-locality`; it changes no unit-level route or realization. The current ancestor statement itself does not purport to prove an ampleness theorem; the recorded `from.place` identifies the existing subordinate input. All new nodes inherit the item's chapter/unit and exact ancestry, adding this item to `via`.

The approximation squares are not assumed Cartesian. Instead of asserting that they are, Step 6 uses the commuting equation to identify the inverse image of the chosen base open, then restricts the affine limit projection. Choosing the stage neighbourhood affine also makes its inverse image in the base affine. Step 7 can therefore prove ampleness on each further affine base open by ordinary affine pullback. This implements the source's final hints directly.

Off-unit statements are generic algebraic-geometry tools: proper base change, proper Noetherian approximation, finite-type Noetherianity, locally Noetherian quasi-separatedness, residue fields/fibres of limits, qcqs over an affine base, affine projections, affine permanence, and affine pullback of ampleness. They are declared in `split_report.tool_uses` where their unit differs. The same-unit line-bundle and morphism-between-affines nodes are reused. No SGA source is cited.

## Not duplicates

Searched the whole DAG and whole blueprint for 0B8W, 09MT, 0D2N, invertible limit/descent, ampleness, and ample Noetherian neighbourhoods before writing. No existing node had the three primary theorem tags 0B8W, 09MT, or 0D2N, or stated a generalization that supplies a child. The first dry run listed twelve collisions on the contextual Situation tag 01YX in the 09MT source citation; I opened every listed statement and compared them below. Existing proper approximation, residue-field limit, and fibre-limit nodes were found and cited rather than recreated.

- `lem-trf-invertible-affine-limit-descent` vs `lem-sc-descended-invertible-neighbourhood`: the latter trivializes a module whose descent along a special morphism is already given; it has no inverse system or finite-stage descent assertion.
- `lem-trf-ample-affine-limit-descent` vs `lem-pc-very-ample-descends`: the latter descends very ampleness along a field extension on one finite-type scheme; it does not handle non-Cartesian inverse systems with affine transitions.
- `lem-trf-noetherian-fibre-ample-neighbourhood` vs `lem-trf-ample-neighbourhood`: the new lemma requires a Noetherian base and is the cohomological finite-stage input 0D2N, whereas the item proves the arbitrary-base theorem 0D2S through three distinct descent/comparison operations.
- `lem-trf-noetherian-fibre-ample-neighbourhood` vs `lem-trf-proper-fibrewise-ample-projective`: the existing parent is limited to families of curves, assumes all geometric-fibre component degrees positive, and concludes a global projective-bundle embedding. It depends on the item and cannot supply the local arbitrary-dimensional Noetherian theorem.

- `lem-trf-ample-affine-limit-descent` vs `lem-sc-valuation-limit-affine-pushforward-colimit`: computes affine pushforwards and tensor colimits for a fixed quasi-coherent module; it asserts no finite-stage ampleness.
- `lem-trf-ample-affine-limit-descent` vs `pqf-lem-limit-qc-open-descends`: descends quasi-compact open subsets and their equalities, rather than ampleness of a specified line bundle.
- `lem-trf-ample-affine-limit-descent` vs `lem-weil-pbc-affine-base-piece-tensor-presentation`: presents affine restrictions of a locally finite type morphism by tensor extension; it states no line-bundle ampleness criterion.
- `lem-trf-ample-affine-limit-descent` vs `lem-weil-pbc-affine-chart-directed-ring-model`: models etaleness on affine charts by a finitely presented ring map; it gives no ampleness assertion.
- `lem-trf-ample-affine-limit-descent` vs `lem-weil-pbc-affine-open-directed-ring-system`: constructs ring systems for inverse images of an affine open; it does not descend ampleness of an invertible module.
- `lem-trf-ample-affine-limit-descent` vs `lem-weil-pbc-affine-over-limit-inclusion`: says inclusion of affine objects over a base preserves a limit cone, without any line-bundle or ampleness assertion.
- `lem-trf-ample-affine-limit-descent` vs `lem-weil-pbc-closed-image-limit-system`: constructs closed-immersion systems for a closed subscheme of a limit, without finite-stage ampleness.
- `lem-trf-ample-affine-limit-descent` vs `lem-weil-pbc-descend-affine`: descends affineness of a morphism obtained by Cartesian base change; our lemma descends ampleness of a specified line bundle on a general affine-transition inverse system.
- `lem-trf-ample-affine-limit-descent` vs `lem-weil-pbc-etale-limit-cohomology-qcqs-gluing`: reduces etale cohomology continuity to affine stages; our statement is Zariski line-bundle ampleness, not cohomology continuity.
- `lem-trf-ample-affine-limit-descent` vs `lem-weil-pbc-etale-limit-tail-open-geometry`: gives limit cones and qcqs properties for restricted open systems, not ampleness at a stage.
- `lem-trf-ample-affine-limit-descent` vs `lem-weil-pbc-limit-affine-transition-affine-comparison`: identifies an affine limit with the spectrum of a colimit of rings, without a line-bundle positivity statement.
- `lem-trf-ample-affine-limit-descent` vs `lem-weil-pbc-limit-affine-transition-core`: asserts existence of scheme limits with affine transitions, not descent of ampleness.

## Mathlib searches

Every child and the item has LeanFinder, LeanSearch, Loogle, and source-grep queries run through the required msearch command. A second semantic phrasing was tried for each. Full outputs are in `search-results.jsonl` and the command's records in `searches.jsonl`; the records in each node use the exact query text. All services responded on this run. No declaration matched. Loogle's unknown `IsAmple` identifier on the inherited pattern is recorded as returned, not described as a failed service.

Read the returned section-descent and affine-open-descent statements, especially `AlgebraicGeometry.exists_appTop_π_eq_of_isLimit` in Mathlib `AlgebraicGeometry/AffineTransitionLimit.lean:842` and `Scheme.exists_isAffine_of_isLimit` at line 1040. These descend structure-sheaf sections or affineness, not an invertible sheaf and its ampleness. The returned generic `HasAffineProperty` criteria assume the property to be established; properness locality/base-change instances do not supply ampleness. The broad grep patterns also returned incidental occurrences of the word “example”. A precise word-boundary ampleness grep and the invertible-descent grep in `AlgebraicGeometry` both returned zero hits, and are recorded as additional searches. The original item's four search query texts were also rerun, with actual outputs retained.

## Review by NU

I checked B through E against the node files and the actual Stacks sources. The item's source is More on Morphisms 0D2S, lines 14153–14196, read in full. Every new statement introduces its own system, objects, direction of transition maps, hypotheses, and pullback; definitions are cited for the notions they actually define. Tags were verified in `tags/tags`. No proof sketch is embedded in a child statement. No Mathlib leaf is claimed.

For Step 1, I opened the proper-base-change statement, which explicitly allows arbitrary base change, and affine-scheme-qcqs, which gives both required base hypotheses. The restriction has the same residue-field fibre at the chosen point. Passing to this affine open does not assume the original base quasi-compact.

For Step 2, the existing proper-approximation node explicitly gives both limits, commuting maps, affine transitions, proper stage morphisms and affine finite-type base stages. The finite-type-over-Noetherian node explicitly includes finite type over Spec Z; it also applies to each proper stage because properness includes finite type. Its definition of Noetherian gives quasi-compactness. The separate locally-Noetherian-quasi-separated node gives the other half of the descent hypotheses; it is not inferred merely from the word proper.

For Step 3, 0B8W(2) gives exactly the invertible stage module and pullback isomorphism needed. The existing invertible-pullback-tensor statement gives both invertibility and composition isomorphisms, so it justifies the compatible later modules. I wrote out why a directed tail has the same cone universal property instead of leaving a cofinality assumption implicit.

For Step 4, the residue-field-limit node states the compatible Spec-limit assertion, and the fibre-product-limit node explicitly states both the fibre limit and affineness of its transitions. Thus no claim about limit fibres is taken from a mere definition. Proper base change and the proper definition give finite type and separatedness of each fibre; qcqs-over-affine then supplies exactly the hypotheses of 09MT on these schemes. The pullback-composition statement identifies the line modules along the commuting fibre squares.

For Step 5, the ampleness-isomorphism node allows the fixed-stage pullback isomorphism to be used in the hypothesis of 09MT. That node gives one index with ample restricted module, which is exactly the hypothesis of the Noetherian lemma 0D2N. The properness and Noetherian hypotheses for 0D2N were established in Step 2. No geometric-fibre versus residue-field-fibre replacement is made.

For Step 6, the limit-affine-transition statement explicitly gives affine projections on both systems. Affine permanence (2) makes U affine, and (1) applies to the restriction of the source projection along the open inclusion of the stage inverse image. The commuting equation identifies this open inverse image exactly; this is the only square used as a pullback here. Affine pullback of absolute ampleness applies without Noetherian or finite-type assumptions on that restriction. Pullback composition and invariance under isomorphism identify the pulled-back line bundle with the original restriction. The absolute-ampleness definition includes quasi-compactness of the source, so this also verifies the item's extra clause.

For Step 7, I read the statement that every morphism between affine schemes is affine. Both W and U are affine, so it applies to their inclusion. Affine permanence gives the base-changed inclusion on Y, and affine pullback of ampleness gives the desired module on each inverse image. Module pullback gives its restriction identification, and the ampleness-isomorphism node makes this precise. I corrected the source label for the morphism-between-affines fact to 01SH after checking the tag map.

The child statements pass the following small-case checks. Constant systems give the original invertible/ample module at the same stage. A one-point scheme with the unit line module and the empty scheme are allowed; 09MT retains qcqs precisely so that eventual affine/cover detection remains valid even when the limit is empty. In the Noetherian lemma, projective space with O(1) supplies the expected affine-base neighbourhood, while O or O(-1) on P^1 fails the fibre-ampleness hypothesis. Zero-dimensional proper fibres are allowed and no positivity assumption is inserted. An empty fibre is harmless: properness makes the image closed, permitting a neighbourhood with empty inverse image. At the item level, the identity of an arbitrary non-Noetherian scheme with the unit module reduces to an affine neighbourhood, confirming that the original base need not be Noetherian or quasi-compact. No step exceeds 2000 characters; each contains a single local operation or the explicit directed-tail argument. The three children are non-elementary inputs, rather than extracted one-line consequences or clauses copied from the item. `citations.json` quotes the cited statements verbatim.

## Unfinished work

None for this one-level split. The three children remain statement-only unsplit nodes as required. No Lean files were written and no compiler, Lake, or build tool was run. The first server dry run requested explicit distinctions for twelve contextual 01YX tag collisions; all twelve statements were opened and the comparisons were added above. The required passing server dry run and delivery are the final validation steps.
