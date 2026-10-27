# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-quotient-section-mate-realization.json`: statement, split into six proof steps; no whole-item Mathlib match. Statement and its statement dependencies are unchanged.
- `citations.json`: eleven verbatim statement quotations, one for every step/node citation.
- `report.md`: this report and the direct-delivery self-review.
- `searches.jsonl`: actual msearch output log. `write_split.py` is sandbox-only preparation material, not a DAG file.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched the whole `lean/WeilConjectures/` for the item's blueprint tag, and the CategoryTheory and SixFunctors sources for internal/section module, derived, tensor and adjunction comparisons. The tag has no hit. Hits such as `ModuleObject/Colimit/Compatibility.lean` concern a field-linear scalar construction; they do not state this simultaneous realization, the specified integral quotient map, or both mate equalities. No sorry declaration was treated as a finished proof.

## WANTED

None. The source material used is present locally.

## Problems found and changes made

The imported item had an empty proof. Its statement is mathematically consistent and was not changed. The natural-language phrase “termwise derived equivalence” in its setup needs the exactness/K-flat dictionary proved in Step 1; the bare definition node supplies only the ordinary reconstruction. I therefore cite the existing theorem `lem-pe-internal-section-tensor-comparison`, rather than claiming that the definition itself proves this dictionary.

The generic scalar comparison writes extension as S tensor M, while the item writes M tensor S. Step 3 explicitly uses the symmetry-preserving tensor comparison on both sides. The comparison consequently preserves x tensor s in the item's convention, without accidentally inserting a reversed balancing map.

The ordinary geometric comparisons are already fixed by `def-pd-section-module-operations-data`. Step 2 uses the existing theorem about the independently derived adjunctions, not a newly transported adjunction that would have to be identified later. Step 4 uses the existing general, non-flat scalar/pullback normalization for the actual finite projection. Steps 5 and 6 expand the mates with their actual units and counits; no exchange/reduction rectangle is asserted or used.

## Existing nodes and route

Before proposing any new node I searched the full DAG by internal/section, K-flat, derived equivalence, scalar and adjunction concepts. I read the statements of the candidate tensor, scalar and geometric normalization nodes in full. `tools/blueprint_refs.py ancestor` gives `det-thm-sfb-proper-base-change-integral`; whole-blueprint searches for `internal section`, `scalar adjunction`, and `derived pushpull` found no statement identifying the whole item. The exact whole-item Lean tag likewise has no hit.

The tensor comparison, scalar-adjunction comparison and geometric derived normalization are generic tools in other units. Their `split_report.tool_uses` entries explain why they serve as realization dictionaries; they do not replace the unit's proper-base-change route. `lem-sfb-internal-scalar-pullback-normalization` is already an existing node in this item's own unit. It gives the arbitrary condensed-ring-map balanced comparison, so creating a quotient-specific replacement would be a duplicate. The original statement dependencies remain necessary for the original unchanged statement.

## Mathlib searches

I ran LeanFinder twice, LeanSearch, Loogle and two source-grep queries through the required msearch command. All six completed successfully, and the exact query texts and results were appended to the existing item's search record; previous searches were retained. I read `SheafOfModules.PullbackConstruction.adjunction` and `pullbackIso` in `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`, and the conjugate/mate composition identities in `Mathlib/CategoryTheory/Adjunction/Mates.lean`. They provide ordinary module adjunctions and abstract mate calculus, not the internally and independently specified unbounded realization in the item. The second semantic query returned ordinary-module flatness tests and sheafification maps, also not a match. No new node requires its own search record.

## Not duplicates

No new nodes. All needed general comparisons already exist and are cited directly.

## Unfinished work

No mathematical clause of the item is left without a proof step. Its dependencies remain separate DAG items where not already finished, as required by a one-level split. Delivery validation is performed by the required server tools; no Lean, compiler, Lake, build, repository write or direct git operation was used.

## Review by O2

I read the chapter and the complete proper-base-change unit before writing the proof. The source for the item is paragraph (3) of the current `sk-thm-sfb-proper-base-change-integral.proof.md`: it says the reductions of the actual canonical maps are the torsion maps. This item supplies the realization dictionary needed for that assertion, rather than its full reduction rectangle. I also read the current module-derived-pushpull unit, which derives the module composites, not their underlying abelian factors. The sources I checked for the generic tools were Stacks `sites-modules.tex`, 03EK (`section-tensor-product`), 0GMW (`lemma-sheafification-tensor`), and 03EL (`lemma-tensor-product-pullback`); `derived.tex`, 09T5 (`lemma-derived-adjoint-functors`) and 08BJ (`lemma-adjoint-preserve-K-injectives`); `sites-cohomology.tex`, 07A6 (`lemma-adjoint`), 07A7 (`remark-base-change`) and 0FPI (`lemma-adjoints-push-pull-compatibility`). The scalar balanced comparison was also checked against the current `det-prop-scalar-six-pullback.proof.md`, part (1). These Stacks passages support the underlying constructions; they do not themselves purport to state the entire simultaneous realization, which is marked as an agent argument.

Step 1 uses exactly the statement of `lem-pe-internal-section-tensor-comparison`. It states exactness, the total-tensor comparison, and preservation/reflection of both flat modules and K-flat complexes. Thus it really supplies preservation of a complex having both properties; no claim about K-flat preservation is inferred from an ordinary equivalence alone. The small-site, coefficient-universe and sheafified abelian-tensor hypotheses are the ones in the fixed reconstruction setting. This supplies the derived equivalences used subsequently.

Step 2 uses `lem-pd-section-derived-pushpull-normalization` and the operation-data definition. I checked the former's statement explicitly includes the independently derived units/counits and geometric pullback compositors, while the latter explicitly identifies its operations as transparent aliases of the existing section constructions. The inputs are a commutative condensed ring, an arbitrary scheme morphism, and the small pro-etale sites. They hold twice, for the integral condensed ring and the finite discrete quotient. In particular there is no improper use of a flat coefficient-change theorem: this is a comparison for each coefficient ring separately.

Step 3 uses the scalar-adjunction theorem for an arbitrary ring-object map a, which explicitly has no flatness assumption, identifies the ordinary generator and scalar units/counits, and specifies localization on flat-term K-flat representatives. The tensor theorem supplies the symmetry compatibility needed to use right-hand scalar tensor. I checked the scalar unit is x mapped to x tensor 1 and the counit is multiplication after this convention change, so this is the same scalar adjunction rather than just an isomorphic left-adjoint functor.

Step 4 uses the statement, not the proof, of `lem-sfb-internal-scalar-pullback-normalization`. It explicitly asserts the internal/section realization of its normalized maps with the geometric units/counits identified. I instantiate its condensed-ring homomorphism with reduction A to A/pi^n; this is continuous and its pulled-back map is precisely the actual finite projection retained in the item. The other citation, `lem-sfb-integral-quotient-direct-image-comparison`, states the forward generator formula fixing lambda. Both therefore refer to the same forward comparison; the reverse mate from the alternative scalar adjunction is not being substituted. Coequalizer equality on balanced generators explains their ordinary agreement, and the cited general normalization supplies the entire unbounded K-flat localization and representative independence. This prevents hiding a separate derived descent assertion inside the generator check.

Step 5 is elementary substitution in the explicit mate definition, using the exact adjunct that the direct-image comparison node states. The displayed formula begins with the S-geometric unit on D_V F_R K, then applies F_S to lambda followed by D_U of the R-counit. Under Steps 2–4 these factors are exactly the section unit, chi, and T_U of the section counit. This is the definition of pr. The cited mate node contains that unit–square–counit formula and the equivalent transpose, so neither naturality of a different comparison nor invertibility is being assumed.

Step 6 is the corresponding elementary substitution in the ambient exchange definition. The first compositor is inverted, then the chosen square equality is used, then the second compositor. Step 2 compares all these geometric compositors with the specified section ones. The last two factors are the h-pullback of the f-counit and the f'-unit, exactly as 07A7 and the cited ambient definition specify. I checked the types: the square map starts at L_f' L_g F_f K and ends at L_h L_f F_f K, so its contraction lands at L_h K and its mate lands at F_f' L_h K. This works for B=R and B=S independently. No assertion that the exchange is an isomorphism enters the substitution.

For the B–E checklist: there are no new statement-only nodes, new definitions or new Mathlib leaves to audit; the unchanged item introduces every object and retains all definition dependencies, all new prose uses single-escaped TeX in JSON, and each of the eleven citations has a verbatim quotation from the node statement. All six steps are below 2,000 characters. The two elementary steps are only explicit formula substitutions, not existence or resolution claims. I checked the transitive dependency closures of the main tensor, scalar and geometric tools and of the general scalar/pullback node: none contains this item, so no self-supporting cycle is introduced. Nothing restates this item as a new node.

I tested the argument on zero complexes, an empty scheme and identity geometric maps. All displayed comparisons then reduce to the corresponding zero maps or adjunction identities. For n=1 the coefficient projection is non-flat in general; Step 3 and the general normalization in Step 4 expressly allow that case. Higher positive n require no new hypothesis. I also checked non-proper scheme morphisms: the source and target comparisons and the mate formulas exist on the whole derived categories; the proof uses no properness or constructibility. The main corrections made during this reading were to cite the tensor/K-flat theorem instead of the bare reconstruction definition, to handle the tensor-order convention explicitly, and to spell out both mate formulas so that equality of the specified arrows can be checked directly.
