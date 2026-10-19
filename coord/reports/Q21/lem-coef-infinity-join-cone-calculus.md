# Stage-1 report: lem-coef-infinity-join-cone-calculus

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-join-cone-calculus.json`: item, statement, split into eight proof steps; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-infinity-cellular-natural-equivalence.json`: new statement, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-infinity-isofibration-exponentiation.json`: new statement, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-infinity-isofibration-base-change.json`: new statement, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-infinity-arrow-morphism-square.json`: new statement, unsplit; no Mathlib match.

`citations.json` records all fourteen step/node pairs with verbatim extracts from the cited statements. `searches.jsonl` is the actual msearch log; `search_plan.json` and `search-output/` retain the queries and returned hits. `write_split.py` is sandbox-only generation code. No Lean, shared-repository, launcher, chapter, or unit file was written.

## Attachments

None. Project searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, item id, fat/blunt join, cone comparison, comma mapping spaces and isofibration terminology found no declaration stating this item. The upstream master checkout is not used as evidence of a finished proof.

## Wanted sources

WANTED: archived Cisinski, *Higher Categories and Homotopical Algebra*, July 30, 2026 revision of https://cisinski.app.uni-regensburg.de/CatLR.pdf, Corollary 1.3.10, Corollaries 2.3.16, 2.3.18, 2.3.29, and Proposition 4.2.3, for the item and lem-coef-infinity-cellular-natural-equivalence.

WANTED: archived Kerodon Proposition 4.4.5.1 (https://kerodon.net/tag/01F1), Corollary 4.4.5.3 (01F3), and Proposition 4.6.1.22 (https://kerodon.net/tag/01P8), for lem-coef-infinity-isofibration-exponentiation and the item's joint endpoint calculation.

WANTED: archived Kerodon Corollary 4.5.3.34 (https://kerodon.net/tag/03PM), for lem-coef-infinity-isofibration-base-change.

WANTED: archived Kerodon Theorem 8.3.7.1 (https://kerodon.net/tag/06BZ), including its oriented-fiber-product conventions, for lem-coef-infinity-arrow-morphism-square.

All these sources were read online in this session. They were not downloaded to the shared project. No Stacks tag supplies these quasicategorical assertions. Kerodon identifiers are explicitly identified as Kerodon tags, including the identifier 01F1 that also has an unrelated meaning in Stacks. The proof is marked `proof_origin.by = agent` because its sources are not archived under literature/. No SGA source is used.

## What was wrong or missing

The item was an unsplit foundation with a correct statement, but its listed sources did not themselves identify the varying-boundary mapping-space theorem. Kerodon Theorem 8.3.7.1 now supplies an independent interval-arrow calculation from which the item's formula is derived. The old maintainer-owned `source.place` still says that this reference is wanted; the maintainer can update that provenance after review. I did not edit the item's source field or statement.

The joint projection cannot be replaced by boundary restriction alone, nor can an arbitrary equivalence be pulled back as an ordinary simplicial map. Step 4 establishes both required isofibrations before applying the general pullback theorem. Step 6 avoids an unproved assertion that pinched mapping spaces preserve an arbitrary strict pullback homotopically: it first uses the degreewise unpinched prism identity, the endpoint morphism Kan fibration, and then the existing natural pinch equivalences.

The current blueprint source for the ancestor is `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, paragraph 2. I read this and its statement, the item's recorded chapter and unit, and the existing source-gluing proof. The inherited ancestry through finite-Reedy localization explains this foundational item. No chapter/unit route is replaced and no unit realization field belongs to this non-key item.

## What remains

The item has a complete one-level split. Its four new foundational statements are deliberately unsplit and have no proofs or proof dependencies. No part of the item's argument is deferred to a new join-cone or general cone-comma lemma. Archiving the online literature and proving the four smaller nodes remain later work, as required by stage 1.

## Not duplicates

lem-coef-infinity-isofibration-base-change vs lem-coef-infinity-join-cone-calculus: the new node concerns an arbitrary equivalence over two isofibrations and an arbitrary base change; it mentions neither cones nor joins and does not construct or prove the item's comparison. Step 4 first constructs and checks the two joint projections before applying this generic theorem.

lem-coef-infinity-isofibration-exponentiation vs lem-coef-infinity-mapping-excision: the existing node states a mapping-space excision formula for a pushout of indexing shapes. It does not assert lifting of equivalences for functor restriction or Kan-fibration lifting for morphism spaces of an arbitrary inner fibration. Shared Kerodon 01F3/01P8 references are infrastructure in the existing node's provenance, not its statement.

lem-coef-infinity-isofibration-exponentiation vs lem-weil-pbc-top-degree-open-restriction-surjective: the existing node concerns top-degree cohomology of a sheaf of modules on a Noetherian scheme. Its Stacks 01F1 refers to underlying abelian sheaves. The new node's Kerodon 01F1 concerns exponentiation of quasicategorical isofibrations; these tags are from different works.

lem-coef-infinity-arrow-morphism-square vs lem-coef-infinity-pinch-comparison: the existing node compares two models of one morphism space and is reused in steps 6 and 8. It does not compute morphism spaces between arrows or the projection to their two endpoint mapping spaces.

lem-coef-infinity-arrow-morphism-square vs lem-coef-infinity-slice-equivalence-final: the existing node characterizes equivalence edges by final objects in a slice and does not compute mapping spaces between two interval arrows or their joint endpoint projection; the shared 01L5 citation only identifies pinched mapping-space models.

lem-coef-infinity-arrow-morphism-square vs lem-coef-infinity-mapping-excision: the existing node glues mapping spaces across a pushout of shapes. It does not give the cross-composition compatibility path for two interval arrows. Shared 01L5 only supplies the mapping-space convention.

lem-coef-infinity-arrow-morphism-square vs lem-coef-infinity-anodyne-cocones: the existing node gives a pushout-join inner-anodyne assertion and restriction equivalence of cocone spaces along a right-anodyne map. It has no interval-arrow mapping-space formula. Shared 01L5 concerns conventions.

lem-coef-infinity-arrow-morphism-square vs lem-coef-infinity-terminal-anodyne: the existing node characterizes a terminal vertex by a right-anodyne inclusion. It does not compute morphisms between arrows. Shared 01L5 concerns conventions.

The other near matches were also read: lem-cbc-enhanced-functor-cone-calculus handles a fixed boundary only, so it cannot supply the varying-boundary formula; lem-coef-infinity-arrow-target-right-fibration concerns arrows with fixed target, not the joint endpoint projection; lem-coef-simplicial-boundary-collapse-test is a Kan-Quillen weak-homotopy criterion, not a categorical-equivalence criterion; lem-coef-simplicial-shape-categorification gives a fibrant replacement with a universal property, not cellular detection of an arbitrary natural transformation. None is a substitute for a new statement here.

Before creating the nodes I searched the entire DAG for their names, key concepts and source tags, and used `tools/blueprint_refs.py search` for cellular equivalence, restriction functor, arrow category, exponentiation, categorical pullback, fat join, join cone, and the Kerodon source tags. The one blueprint restriction-functor hit concerns pro-etale injectives. No blueprint node states a new foundation or the item; all `same_as` fields are empty. The ancestor command gives prop-coef-integral-exceptional-adjoint, retained with the full inherited via chain.

## Review by Q21

I checked the item against Cisinski's cone constructions and the proof of Proposition 4.2.3, and read Kerodon 05YH, 01KG and 03PM to verify the intended orientation and relative claim. I additionally read Kerodon 01F1, 01F3, 01P8 and the full Hom-functor pullback square in 06BZ. The latter is the new source for the interval-arrow foundation: applying its two identity functors gives the arrow category, and its cross term is Map(source of the first arrow, target of the second), exactly the term needed here. The four new nodes isolate cellular detection, exponential lifting, homotopy-invariant ordinary base change, and interval-arrow morphisms. They are independent foundational inputs, rather than new names for four cone clauses.

Step 1 uses only the definition of the internal functor simplicial set in def-cbc-enhanced-diagrams-cones. I wrote out the quotient map, both simplex blocks and the product/pushout universal property. There is no hidden comparison theorem at this step.

Step 2 uses the componentwise-equivalence criterion and functor-category closure in lem-cbc-enhanced-functor-cone-calculus, whose statement I opened. I checked the section and the order inequality on the product poset. The homotopy stays in the collapsed bottom face there and is the identity at every upper vertex, so its component images really are equivalences in any target. It is natural in the variable functor H, yielding the required natural equivalence of endofunctors rather than just objectwise witnesses. The section need not be natural in n or in K.

Step 3 uses precisely the cellular criterion in lem-coef-infinity-cellular-natural-equivalence. I checked the degreewise disjoint-copy descriptions for BOTH functors: each has one constant apex, which commutes with connected colimits but need not commute with the empty colimit. The empty object is consequently a separate hypothesis of the criterion and is checked in step 2. The criterion is the general saturation argument read in Cisinski 1.3.10 and the homotopy gluing corollaries used by the proof of 4.2.3; its eventual proof must use categorical, not merely weak homotopy, equivalences.

Step 4 uses the full restriction-isofibration statement of lem-coef-infinity-isofibration-exponentiation and the common-base theorem of lem-coef-infinity-isofibration-base-change. I verified that the join apex and boundary are disjoint simplicial subsets, that their union inclusion is injective, and that the endpoint restriction is along the boundary of the interval. I wrote out why pullback retains the horn and equivalence lifts. The comparison is strictly over the base by step 1. The new base-change statement makes no fibration assumption on h or on the comparison itself, just as Kerodon 03PM requires only the two projection fibrations. Fixed vertex/boundary cases are actual maps from the indicated quasicategories.

Step 5 uses these same two new statements, with the products constructed coordinatewise. This is a short argument from lifting definitions and the supplied quasi-inverses; it is not a new product node. I checked that the empty product is the point, and that an arbitrary small family can be formed in the chosen larger universe. No finite-product hypothesis was smuggled in.

Step 6 uses three opened statements: lem-coef-infinity-pinch-comparison supplies Kan complexes and the natural pinch equivalences; the morphism-space clause of lem-coef-infinity-isofibration-exponentiation supplies the actual Kan fibration on the right-hand leg; lem-coef-kan-quillen-right-proper explicitly says that replacing a leg by a fibration and taking the strict pullback models the homotopy pullback, independently of that replacement. The formula for U of the pullback follows degreewise from its prism definition, so it needs no separate excision theorem. The right-hand leg is induced by the endpoint functor, whose isofibration was proved in step 4. I checked all four endpoint objects and the direction (a,b) maps to (Delta a,b).

Step 7 uses only the new interval-arrow formula, including its joint endpoint projection; I opened that statement after writing it and copied its actual formula into citations.json. I checked the cross term Z=Map_D(Delta x,G), both compositions, and path direction. The auxiliary endpoint identifications are eliminated by explicit path concatenation and contraction, with the reverse operation obtained by constant auxiliary paths. These operations act on whole path spaces. The final path is reversed to match the ordering M times^h_Z L in the item. No conclusion is inferred from equality of homotopy classes.

Step 8 uses the mapping-space clause of the existing enhanced calculus, the naturality of the existing pinch comparison, and the endpoint naturality of the new interval-arrow formula. The actual collapse map is natural in the shape, independently of the auxiliary simplex sections used to prove its equivalence. This distinction prevents a false claim of a canonical natural inverse to the comparison. The projection to boundary mapping spaces is retained at every substitution.

For the small cases, K empty gives the identity comparison on E and the formula Map_E(x,y) times a point, as required. K a point gives the ordinary interval and its arrow category. For K=Delta^1, the section chooses the initial prism vertex (0,0) and the upper vertices (0,1),(1,1); the homotopy moves only the collapsed bottom face. These check the quotient homotopy used for all n. In an ordinary category nerve the new interval formula reduces to the usual equation b u = v a, while reversing source and target correctly makes the space empty when no endpoint map exists. For a two-object simplicially enriched example with only identity endomorphisms and a Kan space Z of maps from the first object to the second, fixed-endpoint endomorphisms of an arrow z form the loop space Omega_z Z. Thus the path term cannot be replaced by equality of components.

I also tested the hypotheses of the new generic statements. The identity natural transformation satisfies the cellular criterion; a collapse of a nontrivial ordered interval to a point is a weak homotopy equivalence but not a categorical equivalence, so it is correctly excluded by that criterion's simplex tests. An inner-fibration morphism-space map may have empty fibers: a discrete two-object category over the point has no map between distinct objects, and the empty space to a point is still a Kan fibration. No surjectivity was added. For the ordinary base-change statement, dropping the isofibration hypothesis really fails: include one object into the groupoid with two isomorphic objects, take this equivalence over the two-object groupoid and pull back at the omitted object. The pullback is empty on one side and a point on the other. The included singleton projection is not an isofibration, while all projections used in the item are.

Finally I reviewed delivery-errors B through E against the finished files. Every new statement introduces its own variables and meanings, carries definition dependencies, uses single-escaped TeX, has an explicit source, and has no proof or proof sketch. I checked every cited statement rather than borrowing its proof. All non-elementary facts used by a step are in its uses list, including the distinction between the Kan and categorical models. The item statement is unchanged and no dispute or weakened hypothesis is hidden. The new nodes have no path back to the item; the off-unit enhanced calculus is declared as a generic tool in split_report.tool_uses. The Mathlib searches were all run through msearch, including second semantic phrasings. Their actual records are copied without invented hits or availability claims. I read the strongest candidate source declarations: the ordinary hoFunctor product-comparison test, ordinary Arrow.homMk, the inner-horn lifting definitions, and generic model-category pullback instances. None gives a one-line specialization to the new categorical foundations.

## Validation

Sandbox JSON, dependency-union, citation-substring, and unchanged-statement checks passed. Finite order checks of the explicit simplex section and homotopy passed for dimensions zero through four; these are combinatorial checks, with no Lean invocation.

Required command: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q21 lem-coef-infinity-join-cone-calculus --no-push`. Its final terminal result is recorded in the sandbox's `dry-run-result.txt`. READY is issued only after that command prints OK. Nothing is pushed by this worker.

## Earlier second reading (a previous round; superseded)

- Step 1 checked against `def-cbc-enhanced-diagrams-cones` and Cisinski §4.2.1–4.2.2: the degreewise quotient, exponential adjunction, and strict apex/boundary projection are stated explicitly; verdict PASS.
- Step 2 checked against Cisinski Proposition 4.2.3 and `lem-cbc-enhanced-functor-cone-calculus`: the section, the collapsed-bottom homotopy, and componentwise equivalence criterion apply for every standard simplex and for the empty simplicial set; verdict PASS.
- Step 3 checked against Cisinski Proposition 4.2.3 and `lem-coef-infinity-cellular-natural-equivalence`: monomorphisms and connected-colimit preservation are verified degreewise, with the finite join summands identified as the $K_j$ for $j\\leq r$; verdict PASS after wording repair.
- Step 4 checked against `lem-coef-infinity-isofibration-exponentiation`, `lem-coef-infinity-isofibration-base-change`, and Kerodon 03PM: both joint projections are pullback-stable isofibrations and the comparison is strictly over the common base; verdict PASS.
- Step 5 checked against the same two isofibration statements and the product lifting definitions: arbitrary small products and the empty product are handled coordinatewise; verdict PASS.
- Step 6 checked against `lem-coef-infinity-pinch-comparison`, `lem-coef-infinity-isofibration-exponentiation`, and `lem-coef-kan-quillen-right-proper`: the prism pullback has a Kan-fibration leg, so the strict pullback models the homotopy pullback before natural pinch replacement; verdict PASS.
- Step 7 checked against `lem-coef-infinity-arrow-morphism-square` and Kerodon 06BZ: endpoint compositions, compatibility-path orientation, and the auxiliary path-space elimination agree with the displayed $M\\times_Z^hL$ formula; verdict PASS.
- Step 8 checked against `lem-cbc-enhanced-functor-cone-calculus`, `lem-coef-infinity-pinch-comparison`, and the arrow formula: naturality in shapes, ambient functors, objects, and boundary projections is retained; verdict PASS.
- New node `lem-coef-infinity-cellular-natural-equivalence` checked for self-contained hypotheses, categorical-equivalence meaning, Cisinski cellular source, definition dependency, and statement-only form; verdict PASS after adding the explicit degreewise-injective definition.
- New node `lem-coef-infinity-isofibration-exponentiation` checked against Kerodon 01F1, 01F3, and 01P8, including inner/isofibration/Kan hypotheses and the unpinched mapping-space clause; verdict PASS after adding the explicit degreewise-injective definition.
- New node `lem-coef-infinity-isofibration-base-change` checked against Kerodon 03PM: arbitrary base change has exactly the two isofibration hypotheses and no extra hypothesis on the comparison or base map; verdict PASS.
- New node `lem-coef-infinity-arrow-morphism-square` checked against Kerodon 06BZ: the oriented fiber-product Hom square gives the cross term and coherent path, with joint endpoint compatibility; verdict PASS.

Changes made in this second reading: clarified the finite degreewise join summands in Step 3; defined “degreewise injective” inside both new statements that use it to satisfy self-containedness; retained all four smaller nodes as genuine foundational inputs. I also checked the zero object, a point and field-style ordinary nerves, the empty scheme analogue (the empty simplicial set), $K=\Delta^0$, $K=\Delta^1$, $n=0,1$, and the fixed-endpoint and empty-product specializations. No statement dispute was found.

## Second reading by Q21

- Item statement: checked every hypothesis and conclusion against Cisinski §4.2.1–4.2.3, the fat-join construction, and the dependency definition; PASS.
- Step 1: checked the degreewise pushout, quotient simplex description, exponential adjunction, and joint boundary projection against `def-cbc-enhanced-diagrams-cones`; PASS, elementary.
- Step 2: checked the standard-simplex section, the prism map and its vertexwise homotopy against Cisinski Proposition 4.2.3; PASS.
- Step 3: checked preservation of degreewise injections and connected colimits, including the empty simplicial set, against Cisinski Proposition 4.2.3 and the cellular criterion; PASS.
- Step 4: checked both joint projections, endpoint restriction, quasicategory pullbacks, and strict-over-base equality against `lem-coef-infinity-isofibration-exponentiation`, `lem-coef-infinity-isofibration-base-change`, and Kerodon 03PM; PASS.
- Step 5: checked coordinatewise products, quasi-inverses, empty products, and product projections against the two cited isofibration nodes; PASS, elementary.
- Step 6: checked the unpinched prism pullback, endpoint Kan fibration, right-proper homotopy-pullback replacement, and natural pinch replacement against `lem-coef-infinity-pinch-comparison`, `lem-coef-infinity-isofibration-exponentiation`, and `lem-coef-kan-quillen-right-proper`; PASS.
- Step 7: checked the cross-composition maps, path orientation, auxiliary path contraction, and boundary projection against `lem-coef-infinity-arrow-morphism-square` and Kerodon 06BZ; PASS.
- Step 8: checked shape and ambient-functor naturality, mapping-space naturality, and endpoint projection compatibility against the enhanced calculus, pinch comparison, and interval-arrow nodes; PASS.
- New node `lem-coef-infinity-cellular-natural-equivalence`: checked B1–B7, self-contained degreewise-injective and categorical-equivalence definitions, Cisinski source, duplicate searches, and empty/simplex cases; PASS, statement-only.
- New node `lem-coef-infinity-isofibration-exponentiation`: checked B1–B7, inner/isofibration/Kan hypotheses, Kerodon 01F1/01F3/01P8, and fixed-endpoint cases; PASS, statement-only.
- New node `lem-coef-infinity-isofibration-base-change`: checked B1–B7, the two isofibration hypotheses, arbitrary-base-map scope, Kerodon 03PM, and pullbacks over a point; PASS, statement-only.
- New node `lem-coef-infinity-arrow-morphism-square`: checked B1–B7, source/target orientation, coherent path formula, joint endpoint projection, Kerodon 06BZ, and ordinary-category and empty-mapping cases; PASS, statement-only.

Changes made: no mathematical or node-file changes were required after this independent reading. I added this second-reading record only; all four new nodes remain genuine unsplit foundations, and the existing item statement and eight proof steps remain unchanged.
