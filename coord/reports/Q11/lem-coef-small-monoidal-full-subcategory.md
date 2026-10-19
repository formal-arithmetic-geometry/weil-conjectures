# Worker report: lem-coef-small-monoidal-full-subcategory

## Files written

- dag/nodes/sec-six-functors/lem-coef-small-monoidal-full-subcategory.json: statement, split into seven steps; no Mathlib match for the quasicategorical assertion.
- dag/nodes/sec-six-functors/lem-coef-small-cocartesian-model.json: new statement-only unsplit lemma; no Mathlib match. This is a general universe-reduction lemma for fibrations over arbitrary small quasicategories, with no tensor structure or monoidal conclusion.
- citations.json: verbatim statement quotations for every node cited by every numbered proof step.

## Attachments

None. Searched the whole read-only slopmaster2 WeilConjectures tree for the item id, small/monoidal terminology, and monoidal/quasicategory terminology, and checked dag/lean_names_upstream.json. Ordinary monoidal sheaf/derived-category constructions do not state this assertion about monoidal quasicategories. The master checkout is only reference material.

## Wanted sources

WANTED: Hongyi Chu and Rune Haugseng, Free Algebras Through Day Convolution, arXiv:2006.08269v2, Proposition 7.15 final proof paragraph and Remark 7.17, for lem-coef-small-monoidal-full-subcategory. Read online at https://arxiv.org/html/2006.08269v2; no archived copy found under literature/.

WANTED: Jacob Lurie, Higher Topos Theory, Theorem 3.2.0.1 and Remark 3.3.2.3 (especially its property (*′), printed p. 211), for lem-coef-small-cocartesian-model. Read online at https://people.math.harvard.edu/~lurie/papers/HTT.pdf; no archived copy found under literature/.

No Stacks tag states either of these quasicategorical results. The relevant Stacks ordinary-category results do not replace them, and no SGA source is used. The item's expanded proof is explicitly agent-written.

## Problems found and changes

An earlier sandbox attempt already supplied the seven steps, new lemma, citations and searches, but had no report. I retained those materials, compared the item against the current unsplit shared node, and reviewed the proof rather than restarting searches. The statement, statement dependencies and historical blueprint ancestry are unchanged.

The proposed step 4 had cited the functor-equivalence calculus for precomposition by an equivalence edge. That statement only asserts mapping-space equivalences induced by functor equivalences, which is a different assertion. I corrected the citation to lem-coef-infinity-mapping-composition and wrote the inverse, associativity and unit-homotopy argument explicitly. Step 7 continues to use the functor-equivalence calculus exactly for its stated mapping-space conclusion.

I sharpened the new lemma's source to HTT Remark 3.3.2.3, property (*′), where the classification of potentially large fibrations with essentially small fibers is explicitly discussed. Theorem 3.2.0.1 alone is a straightening Quillen equivalence, not a verbatim small-model theorem. HTT 5.4.1.7 concerns local smallness and small collections of objects; it is not used as if it directly shrank a fibration over its base.

The chapter record now names a main-20261017 path unavailable in this machine's literature snapshot. I read its actual record, the unit record, and the available main-20261015 ancestor text. This small categorical tool is below the historical ancestor's finite-coefficient adjunction foundation, not a replacement of the unit's Verdier-duality route. No unit binding or chapter file was edited.

## Not duplicates

lem-coef-small-cocartesian-model vs lem-coef-cocartesian-straightening: the latter assumes a small total category in its statement, including its intrinsic-representative convention. The new lemma starts with a potentially larger total category and essentially small fibers, and produces a small total category over the same base.

lem-coef-small-cocartesian-model vs lem-coef-infinity-small-full-subcategory: the latter produces an equivalence to a small quasicategory for a full subcategory on a small collection of equivalence classes in a locally small ambient category. It does not produce a cocartesian fibration over a specified base or preserve/reflect cocartesian edges.

lem-coef-small-cocartesian-model vs lem-coef-locally-small-infinity-size-calculus: that node bounds colimit closures and retract closures, not a total fibration over a fixed base.

lem-coef-small-cocartesian-model vs lem-coef-generalized-operadic-fibration-replacement: that result factors a map between already small generalized operads as an equivalence followed by a categorical fibration. It neither reduces universes nor applies to arbitrary bases.

lem-coef-small-cocartesian-model vs lem-coef-small-monoidal-full-subcategory: the new lemma says nothing about a full tensor-closed subcategory, the restriction of a monoidal structure, inert relative limits, or a strong monoidal inclusion. Those arguments remain in the item's proof. It isolates the separate general small-presentation input, not a renamed monoidal clause.

Before retaining the new node I searched the whole DAG for size/fiber/cocartesian terminology and HTT 3.2.0.1/5.4.1.7, and ran blueprint_refs searches for cocartesian, monoidal, small cocartesian, small monoidal and essentially small, as well as the ancestor command. No blueprint node states the general universe-reduction lemma. The relevant nearby statements were opened and compared. No same-Stacks-tag pair exists.

## Review by Q11

For the item I read Chu–Haugseng Proposition 7.15 and its proof, Corollary 7.16 and Remark 7.17 online. The source treats compact-object subcategories of accessible monoidal categories; our item is the general restriction argument once tensor/unit closure and essential smallness are hypotheses. It therefore does not need the source's cardinal-enlargement or compact-generation assertions. I read the current definitions of monoidal infinity categories, full subcategories, equivalences, smallness and cocartesian fibrations, not just their titles. In particular the monoidal definition includes the relative mapping-space product axiom, which steps 5 and 7 explicitly verify.

Step 1 uses def-cbc-enhanced-diagrams-cones for the vertexwise definition of a full subcategory and its right-pinched mapping spaces, def-coef-infinity-fibrations for inner-horn lifting, and def-coef-monoidal-infinity-category for the ambient Segal equivalences. Every horn filler stays in the full subcategory because its vertices are already prescribed. Restricting a quasi-inverse of the Segal equivalence works because D is replete. This proves the stated fiber equivalences, not just objectwise surjectivity.

Step 2 uses the actual block-transport assertion of lem-coef-monoidal-block-projection-coherence. I checked that it covers arbitrary base arrows, discards initial/final inputs when necessary, and allows nullary tensors. The induction on block length uses the given tensor unit and binary closure. No compactness or closure under colimits is presumed. It proves ambient lifts land in the restricted subcategory.

Step 3 uses the horn definition in def-coef-infinity-fibrations and the full-subcategory definition in def-cbc-enhanced-diagrams-cones. An ambient cocartesian edge whose endpoints are in E satisfies exactly the same horn-filling tests after restriction. This gives enough lifts for q to be a cocartesian fibration; it does not by itself say inclusion preserves every q-cocartesian edge.

Step 4 supplies that converse. I opened lem-coef-infinity-cocartesian-composition-initiality and verified it asserts both initiality in the lift category and an equivalence of targets in the fixed fiber, not merely uniqueness on components. Its composition assertion applies to the comparison triangle. The corrected lem-coef-infinity-mapping-composition supplies associative and unital composition classes and their restriction to precomposition by an edge; composing with the inverse edge gives the required homotopy inverse on mapping spaces. Since the comparison lies over an identity, lem-coef-infinity-cocartesian-mapping-criterion applies with an inner fibration and proves it ambient cocartesian. All three cited statements say the parts used.

Step 5 uses def-coef-monoidal-infinity-category for the relative-limit formula and def-cbc-enhanced-diagrams-cones for the identical mapping simplicial sets of a full subcategory. Step 4 ensures the inert edges chosen in E are ambient cocartesian, so the ambient formula applies. It includes the empty mapping-space product at n=0. This is direct restriction of an existing formula rather than an uncited inheritance theorem.

For step 6 and the new node I read HTT Theorem 3.2.0.1 and Remark 3.3.2.3, particularly the essential-smallness condition for classifying potentially large fibrations. The new lemma is the cocartesian universe-reduction consequence: classify in the larger universe; essentially small fibers make the classifier land, up to equivalence, in the full essential image of the smaller category of small infinity categories; unstraighten the resulting diagram in the smaller universe over the small base. Classification gives the equivalence over the base and equivalences on fibers; its cocartesian functors preserve cocartesian edges and an inverse reflects them. The lemma states this input without putting that sketch into its statement or proof fields. For the item, def-coef-presentable-infinity-category supplies the meaning of essential smallness. Finite products of a chosen small model of D are visibly small models of D^n, and the opposite simplex nerve is small. These are precisely the hypotheses of the new node. The ambient definition already puts the total simplicial set in the larger universe. Local smallness is not silently used as a substitute for essential smallness of the fibers.

Step 7 uses the new model from step 6 and the already proved relative-limit formulas. I checked lem-cbc-enhanced-functor-cone-calculus explicitly says every functor equivalence induces mapping-space equivalences. The base mapping spaces are discrete, so a weak equivalence over them restricts to a weak equivalence on each union of components over a fixed arrow. The monoidal definition's relative products therefore transfer. The fiber equivalence C→D composed with the full inclusion has exactly the replete essential image D, as required. This proves the final strong-monoidal and fully-faithful claims as well as the small model's monoidal axioms.

For edge cases I checked n=0, n=1, empty blocks, arrows discarding boundary inputs, and D containing only the equivalence class of the unit when tensor closure holds. D cannot be empty under the item's unit hypothesis. For the new general lemma, an empty base forces E empty and has the empty small model; a point base reduces to an essentially small quasicategory; empty fibers along a cocartesian transport cause no assertion that a nonempty source transports into an empty target. The hypotheses exclude that situation. Non-small discrete fibers would fail essential smallness and are correctly excluded.

The Mathlib searches in searches.jsonl were read and reused. They include two natural-language phrasings for the new node, Loogle SmallModel, and source grep, plus LeanSearch. I read Mathlib CategoryTheory/EssentiallySmall.lean, FiberedCategory/Cocartesian.lean, Monoidal/Subcategory.lean and AlgebraicTopology/Quasicategory/Basic.lean at the candidate declarations. The first three concern ordinary categories; the last defines quasicategories but does not give this theorem. No hit is an exact match or a one-line specialization. Recorded unavailable/invalid-query outcomes were not turned into claims of absence. No unrun query was added.

I checked delivery-errors B–E against the retained files: the only new node introduces every object, has empty proof/dependency fields for its proof, cites its definitions, has actual logged searches, and has precise blueprint ancestry. All non-elementary steps cite statement-level facts. The elementary steps are the written horn/fullness or formula-substitution arguments. Every step is below 2000 characters. There is no Lean writing, compilation, SGA route, or live-tree modification. The generic off-unit functor calculus is declared in split_report.tool_uses.

## Unfinished work

No part of the item's split remains unfinished. The new general small-presentation lemma is intentionally statement-only and joins the stage-1 queue. Source archival requests remain as listed above. The required dry run and push are performed after this report is written.
