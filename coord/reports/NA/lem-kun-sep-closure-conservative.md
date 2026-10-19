# lem-kun-sep-closure-conservative

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-sep-closure-conservative.json`: existing statement node, split in six steps; no exact Mathlib match for the whole item.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `report.md`: this report. `searches.jsonl` was written by the required search command.

There are **0 new nodes and 0 new Mathlib leaves**. The split reuses the existing Mathlib leaf `lem-weil-pbc-algebraic-extension-embeds-algebraically-closed` and the existing geometric-stalk, inverse-image, and exact-functor nodes.

## Attachments

None for this item. Searched `WeilConjectures/` in the read-only slopmaster2 source by the blueprint id, separable-closure terms, geometric-point terms, and conservativity/isomorphism terms. Read `SixFunctors/Etale/UpperLowerStar/Surjective.lean`: `AlgebraicGeometry.Etale.reflectsIsomorphisms_upperStar_of_surjective` proves a general module-sheaf conservativity result, but does not state the geometric-point factorization or the derived clause of this item. Read `SixFunctors/Etale/Derived/GeometricPoint.lean`: its extensionality results concern morphisms between objects concentrated in degree zero, not this item's unbounded isomorphism criterion. No complete attachment was found. Upstream master was searched as reference material, never treated as proof completion.

## WANTED

None. The shared checkout lacks the untracked literature contents, but the existing read-only literature copy at `/home/ubuntu/work-bp/sheaf/literature/` supplied the exact blueprint and Stacks TeX files. No document was downloaded or written.

## Corrections and dependency audit

The imported statement is true and unchanged. Its proof's phrase that the algebraically closed field “contains” the separable closure concealed a choice of a compatible embedding. Step 1 supplies that embedding using an existing theorem; step 2 constructs the lift by the universal property. This is a proof clarification, not a statement dispute or a departure from the unit route.

The statement dependencies now explicitly cover schemes, separable closures, geometric points, scheme base change, the small etale site, abelian sheaves, derived categories, and the ordinary and derived inverse-image functors. The broad conventions node and the stalk-definition node were unnecessary as direct statement dependencies: the statement does not use stalks, and the precise definitions now replace conventions. The original three proof results remain cited. Added dependencies say exactly the field-embedding, fibre-product, composition, and exact-derived-functor facts that were previously implicit.

`lem-weil-pbc-derived-inverse-image-composition` is restricted to bounded-below derived categories. It was read and deliberately not used to justify an unbounded assertion. Step 4 instead constructs the comparison degree by degree and passes its naturality through localization. No resolution, boundedness, coefficient-category change, finite type, properness, or algebraicity of Omega over K is assumed.

## Unfinished work

None for the authorized one-level split. Existing unsplit dependencies remain existing work items; no node was silently split or altered. The item's unit is not its key statement node, so no unit realization fields are changed.

## Not duplicates

No new nodes. Whole-DAG searches found the existing algebraic-extension embedding leaf before any new-node creation. Whole-blueprint searches for `separable closure`, `sep-closure`, `base change.*conservative`, and `Every geometric point` found no second node with the item's complete statement. The other separable-closure hits define the field or treat Picard descent and are not equivalent conservativity statements.

## Review by NA

I read the original item's statement and proof at `blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-sep-closure-conservative.md` in the existing literature copy, the chapter record and the Kunneth unit record. The unit has no separate proof-step list to replace; this split follows the imported factorization-and-stalk route. I read Stacks `fields.tex`, Tag 09GU (`lemma-map-into-algebraic-closure`), including its Zorn proof; `schemes.tex`, Tag 01JP (`definition-fibre-product`); `etale-cohomology.tex`, Tags 03Q1 (`lemma-stalk-pullback`) and 03PU (`theorem-exactness-stalks`), with their proofs; `topologies.tex`, Tag 021J (`lemma-composition-etale`); and `derived.tex`, Tag 015F (`lemma-right-derived-exact-functor`). There are no new-node sources to review.

For step 1 I opened the full statements of `def-weil-geometric-point`, `def-weil-affine-spectrum`, `def-kun-separably-closed`, and `lem-weil-pbc-algebraic-extension-embeds-algebraically-closed`. They respectively provide algebraic closedness of Omega, the ring map corresponding to the structure morphism, algebraicity of the chosen separable closure, and extension of the specified K-map to that algebraic extension. Stacks 09GU is written with an algebraic closure as target; its proof only uses target algebraic closedness, and the existing leaf explicitly states and Mathlib `IsAlgClosed.lift` proves that generality. I read the cited Mathlib declaration around line 350. We require no literal containment and no separability or finite-generation condition on Omega/K.

For step 2 I checked the affine-spectrum statement's functoriality, `def-pc-fibre-product`'s universal property for arbitrary compatible maps from a scheme, `def-pc-base-change`'s definition of the base change, and the geometric-point definition. The equation of K-maps gives the required commutative square, and the same Spec Omega is the domain of the lift. The universal property does not require an etale or finite base extension. The only elementary work here is applying that property to the compatible pair; no separate lift lemma is needed.

For step 3 I read `lem-weil-pbc-inverse-image-composition` clause (2), which explicitly supplies a natural isomorphism between the composite inverse image and the inverse image of a composite scheme map. I read `lem-kun-stalk-as-pullback`, which identifies the pullback along a geometric point with its stalk, and `lemma-weil-pbc-geometric-stalk-conservative`, which detects precisely isomorphisms of abelian etale sheaves on all geometric stalks. These statements give what the step uses: the first is not merely a definition of inverse image, and the third is not a definition of a conservative family. Applying a functor to an inverse and conjugating by a natural isomorphism is elementary. The sheaf-detection node is a generic tool from another unit; it is already Lean-closed. The inverse-image composition result is declared as an off-unit generic tool because this unit has no separate composition lemma.

For step 4 I opened `prop-weil-pbc-inverse-image-exact`, `lem-weil-pbc-exact-functor-derived-factorization`, and `def-weil-pbc-derived-inverse-image`, in addition to the composition node. The exactness result quantifies over every scheme map; the factorization leaf explicitly covers every complex and the unbounded derived category; and the definition records that construction before restricting it to D+. I wrote the differential compatibility equation so the chain-isomorphism assertion can be checked directly. Naturality for localized morphisms follows from naturality for chain maps and for their inverses when quasi-isomorphisms are inverted. This is elementary work from these cited statements, not an unproved general coherence lemma or an appeal to the bounded-below composition node. The derived-inverse-image definition is also declared as a generic tool to make the interpretation visible to route review.

For step 5 I read the complete statement of `lem-kun-stalk-faithful-derived`: it detects isomorphisms in D(T_Et), without boundedness. The lifted point has the required algebraically closed domain, and step 4 identifies its composite inverse image with the original point's inverse image naturally in the derived morphism. Thus the criterion applies with T=X. Step 6 writes the two inverse equations that every functor preserves, covering the forward implication in both categories without another theorem.

I checked B–E against the final files: no new statement-only nodes or duplicate/clause nodes are needed; all notions have their precise statement dependencies; TeX has single backslashes in the mathematical strings; sources name tags and labels; every non-elementary fact is carried by a cited statement; the quotation file copies those statements verbatim; and no cited node depends back on this item. I corrected the hidden embedding choice and the missing composition argument rather than moving either clause into a new node. For edge cases I checked X empty (factorization is vacuous and both stalk criteria apply), K already separably closed (the same embedding argument applies to the chosen closure), imperfect K in positive characteristic (only algebraicity of L/K and algebraic closedness of Omega are used), and unbounded complexes in both directions (the termwise argument uses no truncation). The lift is generally nonunique, which is harmless because only existence is asserted.

Mathlib searches were run only through `msearch.py` and recorded exactly, with a second conceptual phrasing. LeanFinder and Loogle ran; LeanSearch returned Internal Server Error and is recorded unavailable. The local hit `Scheme.isConservative_pointSmallEtale` was read: it provides the general covering family of points criterion, not all clauses of the item in one specialization. The dry run is the final verification; this worker does not push.

## Second reading by NA

- Item statement: checked against the blueprint node and its source paragraph; the scheme-over-field hypotheses and both sheaf/derived conservativity clauses agree, including the empty scheme and (K=K^{\mathrm{sep}}) cases; verdict: unchanged and true.
- Step 1: checked against geometric-point, affine-spectrum, separable-closure, and algebraic-extension embedding statements and Stacks Tag 09GU; the chosen (K)-embedding into the algebraically closed geometric-point field supplies the lift datum; verdict: correct.
- Step 2: checked against the affine-spectrum, fibre-product, base-change, and geometric-point statements and Stacks Tag 01JP; the compatibility equation gives the universal-property morphism and no uniqueness is assumed; verdict: correct and elementary.
- Step 3: checked against the inverse-image composition statement, stalk-as-pullback statement, and geometric-stalk criterion, with Stacks Tags 03Q1, 03PU, and 021J; the comparison transports the inverse and detects the sheaf morphism at every point; verdict: correct.
- Step 4: checked against exact inverse image, exact-functor derived factorization, derived inverse-image definition, and composition statements, with Stacks Tag 015F; termwise chain naturality and localization cover the unbounded category; verdict: correct, but substantial, so marked non-elementary.
- Step 5: checked against the unbounded derived geometric-point criterion and the comparison from step 4; verdict: correct for every geometric point.
- Step 6: checked directly from functoriality and the two inverse identities; verdict: correct and elementary.
- New nodes: none; consequently B1--B7 and duplicate-node checks are vacuous. Existing dependency statements were opened and each citation quote was compared verbatim with its node.

Changes made in this second reading:

- Marked step 4 `elementary: false`, because its chain-map naturality and passage through localization are a substantive argument rather than a two- or three-line consequence.
- Declared the existing generic exactness theorem `prop-weil-pbc-inverse-image-exact` as a proposed tool use in `split_report`, for maintainer review alongside the existing composition tool.
- Independently searched with `msearch.py` using algebraic-extension embedding phrasing, `"IsAlgClosed.lift"`, and the generic stalk/derived declarations. Read `IsAlgClosed.lift` at Mathlib/FieldTheory/IsAlgClosed/Basic.lean:350, `mapDerivedCategoryFactors` at Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:41, and `Scheme.isConservative_pointSmallEtale` at Mathlib/AlgebraicGeometry/Sites/EtalePoint.lean:126. These confirm the existing tools and supply no leaf for the whole item. The actual search output is appended to `searches.jsonl`.
- Added this section documenting the statement, source, hypothesis, edge-case, citation, and step audit; no statement, dependency, or citation text was otherwise changed.
