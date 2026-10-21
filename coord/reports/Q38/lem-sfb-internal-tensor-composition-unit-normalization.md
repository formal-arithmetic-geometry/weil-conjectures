# Stage-1 report: lem-sfb-internal-tensor-composition-unit-normalization

1. Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-internal-tensor-composition-unit-normalization.json`: existing statement, now split into seven steps; no statement change. Mathlib has the ordinary-module comparison and generic adjoint uniqueness, but neither states the complete internal-module multiplication comparison with this normalization.
- `citations.json`: one verbatim statement excerpt for every cited node in every proof step.
- `report.md`: this report. The required search command generated `searches.jsonl` in this sandbox.
- New nodes: 0. New Mathlib leaves: 0.

2. Attachments

None. I searched the project Lean source by the full item id, by `extendScalarsComp`, the unit/adjunction terminology and tensor/composition terminology. `CategoryTheory.Mod.extendScalarsComp` in `lean/WeilConjectures/CategoryTheory/ModuleObjects/ExtendScalars.lean:463` gives a natural isomorphism in the opposite direction by `leftAdjointUniq`. It does not state the explicit coequalizer multiplication and inverse formulas or the complete unit-normalization conclusion. Thus it is useful source material, not an exact attachment for this item. The individual closed source formulas for the unit and for maps out of an extension do not together directly state the composition multiplication clause either.

3. WANTED

None. The blueprint, internal scalar-extension source and Stacks Categories Tag 0B65 are available locally.

4. Findings

The imported statement is correct and remains unchanged. Its proof was empty. The blueprint sentence “Extension of scalars is compatible with composition” does not supply its underived multiplication calculation, and `sk-def-sfb-change-of-scalars` alone does not state the unit formula. I therefore cite the existing smaller node `def-sfb-modobj-extend-restrict-adjunction`, whose statement actually specifies that formula and its linearity and natural Hom bijection. No mathematical dispute or route change is needed.

The chapter and unit records were read: `sec-six-functors-basics`, `sk-thm-sfb-qlbar-two-colimit`. The proof realizes the unit’s scalar-extension transitivity comparisons, the first paragraph of the ancestor `lem-sfb-constructible-cocone-hom-surj`, and the underived sentence in `def-sfb-derived-extend-comp-iso.proof.md`. It introduces no alternate descent or derived route. This item is not the unit’s key statement, so no unit record is changed. Off-unit citations are declared individually in `split_report.tool_uses`: they define the scalar-extension objects, actions, units and generic universal properties already required by this comparison.

5. Unfinished work

None in this split. Existing dependency nodes retain their own states and are not modified. No Lean file was written and no compiler or build tool was run.

## Not duplicates

No new nodes were created. I searched the whole DAG and `tools/blueprint_refs.py` for scalar extension, composition and coequalizers. The existing `def-sfb-modobj-extension`, `def-sfb-modobj-extend-restrict-adjunction`, `def-sfb-modobj-restriction`, `sk-def-sfb-module-objects`, `sk-def-sfb-ring-object`, `def-weil-pbc-category-colimit`, and `lem-weil-pbc-conjugate-iso-unit-equation` give exactly the needed ingredients. The relative-tensor monoidal structure is not used as an unproved mixed-ring associativity theorem. The extension-along-isomorphism quotient formula has a stronger invertibility hypothesis and was not applied to general coefficient morphisms. No other blueprint node found states this complete comparison, so the item’s `same_as` is `[]` and its existing ancestor and via chain are retained.

## Review by Q38

I read the current blueprint’s `def-sfb-derived-extend-comp-iso.proof.md`, its unit and chapter, and the source-library construction `ExtendScalars.lean:200–467`, especially the induced first-factor action (223–229), unit (321–350), Hom equivalence and adjunction (410–435), and composition comparison (463–467). I also read the Mathlib `leftAdjointUniq` unit equation, the ordinary `ModuleCat.extendScalarsComp` and its unit formula, and `Bimod.TensorBimod`’s coequalizer/action definitions. The generic adjoint tool is the existing Mathlib leaf; I read its full node statement and Stacks `categories.tex`, lemma-transformation-between-functors-and-adjoints (Tag 0B65), including the Hom-set argument. The detailed coequalizer calculation here is my argument, so `proof_origin.by` is `agent`.

For step 1, the extension node actually gives all three coequalizers, the first-factor actions and functorial arrows. The adjunction node states the unit as insertion of the algebra unit followed by the coequalizer and states its linearity. Its specified Hom bijections compose as `f -> fb -> fba`, so the composite unit is `ba`; this is not taken from the mere name “adjunction”. The restriction node explicitly says the underlying objects and arrows are unchanged.

For step 2, I expanded the definition of the induced first-factor action to the equation with the inverse associator and then substituted the already specified unit. The right-unit axiom and monoidal triangle identity give each projection from its action on that unit. This is a short definition-level calculation, not an omitted tensor-associativity theorem. The ring-object statement gives the actual two-sided unit axiom. No new node is warranted for this computation.

For step 3, I read the generic uniqueness node’s unit equation, including its common-right-adjoint special case. Both adjunctions have exactly that right adjoint after the identity-on-underlying-arrows restriction comparison. The extension hypotheses hold for each use: coequalizers and preservation on both sides are assumed; the sources of the extensions are R, S and R, all commutative as required. The target T need not satisfy any extra flatness, invertibility, exactness, closedness or equalizer assumption.

For step 4, I checked that b is S-linear into the restriction of Q, and that the T-linear comparison is S-linear after restriction. Their composite h is therefore an S-module morphism, so the cited module-morphism definition gives the displayed equation for hq. Substitution of c and the induced T-action gives r(psi tensor M) by the same right-unit calculation. I corrected an initially compressed intermediate formula by writing the full typed associator composite; this is now an equality of arrows S tensor M -> H, with no use of generalized elements.

For step 5, the module-morphism definition justifies moving v through the T-action. Substituting the previous equality gives the actual map from T tensor (S tensor M) induced by multiplication in T; the inverse associator has precisely that source. Its factor exists because the already constructed T-linear v has the displayed precomposition. Uniqueness uses exactly the colimit node’s universal property. Tensoring the inner coequalizer preserves it by the stated hypothesis. I wrote out the cancellation argument from uniqueness of a factor, rather than using a theorem that a general epi stays epi under tensoring. The coequalizer indexing category is finite and small.

For step 6, composing vba=c with its inverse gives wc=ba. Applying T-linearity and the three action-on-unit identities yields wr=p(T tensor a). The expanded arrow has source T tensor M and target Q and is exactly the inverse formula in the item. Its two inverse identities are those of the already constructed isomorphism. No unproved “balancedness” calculation or extra descent lemma is smuggled into this step.

For step 7, naturality belongs to the already existing natural isomorphism v. The computed formula identifies the specified multiplication comparison with it, so the proof does not infer naturality from pointwise choices. I checked the equality of units after restriction on the actual underlying arrows. Generic uniqueness then identifies the specified natural isomorphisms. The source-library comparison starts with the direct adjunction as its first argument and the transported composite as its second, so its direction is D -> BA; our multiplication comparison is its inverse.

I checked delivery-errors B–E against the files. There are no new statement-only nodes to audit, no clause moved into a new lemma, no missing non-elementary tool, and no cited node whose proof rather than statement is used. Each citation has a verbatim statement excerpt in `citations.json`. All seven steps are below 2000 characters; their local calculations are written out, and the two non-elementary adjunction constructions cite the applicable statements. The statement dependencies are unchanged because the statement itself already specifies both change of scalars and unit-compatible uniqueness.

For edge cases, identity coefficient morphisms give the usual action/unitor comparison; R=S=T gives multiplication on a regular extension; a zero M in an ambient category with a zero object satisfies the same equations. None of these tests requires that tensor symbols represent elements. The proof never assumes concreteness, faithfulness of global elements, an abelian category, a symmetric braiding, or any finiteness/flatness property. The second semantic Mathlib phrasing returned the general bimodule coequalizer/action ingredients, not this full scalar-extension comparison. All five fresh searches were run with the required command, read, and retained with their exact query text; the original node’s search records are preserved as well.
