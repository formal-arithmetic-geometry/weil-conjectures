# Worker report: lem-sfb-module-direct-image-open-pasting

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-module-direct-image-open-pasting.json`: statement, split; eleven proof steps, no new nodes, no new Mathlib leaves. The statement itself is unchanged. Added explicit statement dependencies for module objects, fibre products and the specified module pullback compositor, all notions already present in its text.
- `citations.json`: twenty verbatim statement extracts, one for each step/node citation.
- `searches.jsonl`: five actual searches for this item through the required msearch command. Existing searches inherited with the item are retained in its JSON, and the five current searches have been appended there.

There was no earlier item copy, split or report in the sandbox. Work began from the live unsplit node. `prepare.py` is an item-local preparation script, not a delivered project file.

## Attachments

None. Searching `lean/WeilConjectures/` for the exact blueprint tag found none. The relevant project declarations `AlgebraicGeometry.ProEtale.CondensedRing.lowerStarComp_assoc`, `lowerStarComp_id_left` and `lowerStarComp_id_right` in `SixFunctors/ProEtale/ModuleObject/UpperLowerStar/Coherence.lean` prove composition and unit laws, not the item's open-slice normalization and successive-open and mixed-pasting clauses. They cannot attach this entire item. The derived open lower-shriek base-change statements have different functors, domains and hypotheses.

## WANTED

None.

## Corrections and route

No statement dispute, removed hypothesis, added hypothesis, weakened conclusion or source error. The imported item had no proof. The important typing issue is that the existing open-comparison theorem uses actual inverse-image coefficient rings, while the item uses the independently pulled-back rings. Step 4 explicitly proves the coefficient square needed to transport its result; applying the old theorem directly to the condensed module categories would miss that check.

The item's inherited unit is `sk-cor-affine-space-rational`, and its nearest blueprint ancestor, verified by `blueprint_refs.py ancestor`, is `det-cor-affine-space-rational-induction`. I read the chapter and unit records and the ancestor's composition-mate step. The intermediate lower-shriek composition route calls for underived direct-image/open-restriction coherence. The supporting blueprint proof is `main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-comp-composition/sk-thm-sf-comp-composition.proof.md`, paragraphs “Composition isomorphism” and “Canonicity and associativity”. This split supplies that underived tool and makes no claim about derived categories. It does not change the affine-space unit's statement or route, and this helper is not its key statement node; no unit record is changed. `blueprint.from` retains the verified ancestor and via chain, its place is already specified, and `same_as` remains empty after whole-blueprint searches for open restriction, pasting, direct image composition, module direct and coefficient morphism. Those searches found narrower or differently typed results, not this combined statement.

All off-unit proof citations are declared in `split_report.tool_uses`, with what their statements supply. They are generic sheaf/module constructions or coefficient identities used by this underived computation; no alternative geometric route replaces a step of the affine-space induction.

## Mathlib assessment and duplication check

The current searches used leanfinder twice with different formulations, Loogle for `SheafOfModules.pushforward_assoc`, the required grep for `pushforward_assoc|pushforwardComp|restrictFunctorComp` in `Algebra/Category/ModuleCat`, and leansearch for direct image/open restriction coherence. All five services/commands returned successfully. I read `Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:139-223` and `PullbackContinuous.lean:168-200`, including `pushforwardComp`, its section formulas, `pushforward_assoc`, `pushforwardNatTrans`, `pushforwardNatTrans_comp` and `pullbackComp`. They provide general compositors and transformation calculus. Identifying the open inverse image, the internal-module representation, the coefficient square and the specified comparisons is additional mathematics; the entire item is not a one-line specialization of any hit. The Zariski `Scheme.Modules.restrictFunctorComp` hits concern structure sheaves, not these pro-etale condensed coefficient modules.

## Not duplicates

No new node is proposed. Existing nodes are reused for all the non-elementary inputs. The associativity, successive-open and mixed-pasting arguments are written as projection calculations in the item rather than relabelled as new clauses/nodes. The derived parent is not used in the proof, avoiding a cycle.

## Review by Q10

I read delivery-errors B through E and checked the completed node against each class of fault. There are no new-node statements or Mathlib leaves needing a separate small-case or declaration-line audit. The full statement and its hypotheses are retained; only explicit notion dependencies have been added. I checked the original blueprint proof and the actual source constructions in `proetale.tex`, Tag 09A5 (`section-morphism`), `sites.tex`, Tag 00XZ (`section-localize`), and `sites-modules.tex`, Tags 03D3 (`lemma-adjoint-push-pull-modules`), 03D6 (`definition-pushforward`) and 03DH (`section-localize`). These sources supply the constructions, not the four coherence equations verbatim. Accordingly `proof_origin.by` is `agent`. I also read the existing tensor-structure blueprint node and the statement of every cited DAG node; no part of an existing proof is used as though it were its statement.

Step 1 uses the tensor-structure node for strong monoidal sheafification, the section-ring coherence node for the internal/sectionwise comparison and its explicit scalar action, the finite direct-image definition for evaluation on the base change, and the module-object definition for the description of morphisms. The representatives are small in the common coefficient universe and coefficients are abelian sheaves, as required. The tensor node supplies the monoidal sheafification assumption of the section-ring result. This avoids the false assumption that evaluation itself preserves tensor products. Equality of module maps follows from the actual definition of a module morphism, not an uncited faithfulness theorem.

Step 2 reads the statements of both compositors: the module compositor explicitly lifts the sheaf compositor, and the latter explicitly names the fibre-product map. The fibre-product definition supplies the projection-preserving uniqueness needed for naturality. The inverse used in this item has the correct direction from the composite direct image to the iterated direct image.

Step 3 takes only the equivalence intertwining actual inverse image and slice restriction from the ringed-open-comparison node. The continuous-functor sheaf-pullback adjunction node specifies the Kan-extension and sheafification adjunctions themselves. Their unit is the coprojection indexed by the distinguished identity arrow. For an object factoring through the open, restriction along its canonical fibre-product projection evaluates that generator as the same section. This proves the unit normalization, rather than assuming it from the bare equivalence in the ringed-open-comparison statement. The eta definition says exactly that eta is this unit followed by the pushforward of alpha. The operations node explicitly supplies the isomorphism for extension along an invertible coefficient map and both of its formulas. Thus the transported action is the one in the statement, not an unspecified identification.

Step 4 uses the eta composition node twice, for the two equal composites of the open square. That node fixes its compositors by exactly the same fibre-product/mate normalization as the definitions cited here. After identifying products, its equation becomes `b_A eta_f,V = eta_f_U,V a_V`. I checked source and target rings in this equation: they run from `Lambda_T(V)` to `Lambda_S_U(A)`. Inverting the two open coefficient isomorphisms then gives the two scalar expressions in the proof. No constant, discrete or finite coefficient premise is introduced.

Step 5 uses the exact statement of the existing open-restriction-counit node: it allows an arbitrary morphism of schemes and arbitrary commutative ring sheaf and provides the stated fibre-product evaluation. I first restrict M's action along alpha_f, so it really is a module over the actual inverse-image ring required by that node. Step 4 proves that changing the endpoint ring actions gives the desired module map. Bijectivity plus linearity proves linearity of its inverse directly. This establishes the specified beta and does not substitute an arbitrary natural isomorphism.

Step 6 proves (b) by giving the common iterated product and comparing both projections to the source product. Only the universal property of fibre products is used beyond previous steps. Step 7 checks the canonical pullback comparisons needed by (c): the eta composition equation specializes to the open coefficient equation, and the elementary scalar-extension comparison carries the composite unit to the single unit. The module pullback-compositor node characterizes its comparison by precisely this adjunction compatibility. Thus it is the specified comparison and acts as identity on the section coordinates. This calculation is necessary to avoid silently choosing a different compositor.

Step 8 proves (c) by displaying the single map and the composite through the intermediate open product and equating their two projections. Step 9 proves (d) by writing the common source and target section groups and checking the two maps' projections to X and V. Both use the uniqueness clause of the fibre-product node, which I quoted, not an unrecorded pasting lemma. Once linearity has been established, equality on sections implies equality as module maps by step 1.

Step 10 uses the eta identity node exactly for its stated identification with the inverse of the direct-image identity, and then applies the already computed maps. I tested identity f, identity j, a composite with either identity factor, and empty U (including empty W and empty schemes). The computations are projection-preserving identities in every case, without a properness, quasi-compactness, nonempty-site, boundedness or finite-coefficient assumption. For example, no argument uses the existence of a nonempty test object over an empty open. Step 11 cites the complex definition only for morphisms commuting with differentials; naturality applied to each differential proves the displayed cochain-map equation and hence all degreewise identities.

Every citation has a specific verbatim statement extract in citations.json. The union of the eleven steps' uses is proof_deps. Every step is below 1200 characters, so none crosses the 2000-character review threshold or hides an inline independent comparison theorem. The coefficient calculation and unit normalization are direct applications and explicit elementary computations with cited constructions. There are no newly stated auxiliary clauses replacing the item's proof, and no dependency on the derived parent. No Lean compiler or Lake tool was run. No Lean file, repository file, launcher file or contract script was changed.

## Unfinished work

None in the mathematical split. Required server validation and delivery follow this report.
