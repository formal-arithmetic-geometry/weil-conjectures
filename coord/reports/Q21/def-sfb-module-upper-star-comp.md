# Worker report: def-sfb-module-upper-star-comp

## Files written

- `dag/nodes/sec-proetale-coefficients/def-sfb-module-upper-star-comp.json`: definition, Mathlib leaf. The complete corrected construction specializes `CategoryTheory.Adjunction.leftAdjointCompIso` (Mathlib/CategoryTheory/Adjunction/CompositionIso.lean:72) by taking its inverse. No new nodes.
- `citations.json`: empty list, because a Mathlib leaf has no proof steps.
- `report.md`: this report. `searches.jsonl` was written by the required search wrapper.

There is one Mathlib leaf in this delivery, the item itself; zero newly created leaves.

## Attachments

None. Searched the whole `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item tag and `CondensedRing.upperStarComp`, and searched the pro-etale source for the notion. The ModuleObject directory and the named declaration are absent from this checkout. The underived plain-sheaf composition comparisons have a different coefficient category. The newer reference master has `AlgebraicGeometry.ProEtale.CondensedRing.upperStarComp` at `WeilConjectures/SixFunctors/ProEtale/ModuleObject/UpperLowerStar/Defs.lean:300`, but it is not an attachment: this checkout is reference material, not finished-proof evidence.

## WANTED

None. The blueprint, relevant Stacks source, and pinned Mathlib declarations were available locally.

## Source error

STATEMENT-DISPUTED: the imported node says that
`b : h^* ≅ f^* ∘ g^*`, for `h = g ∘ f`, is conjugate to the inverse of
`c : g_* ∘ f_* ≅ h_*`. This has the wrong type under the project's existing definition of conjugation.

Write `L₁ = f^* ∘ g^*`, `R₁ = g_* ∘ f_*`, `L₂ = h^*`, and `R₂ = h_*`.
For `a₁ : L₁ ⊣ R₁`, `a₂ : L₂ ⊣ R₂`, the conjugation equivalence is
`(L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂)`.
Thus the conjugate of `b.hom` is of type `R₁ ⟶ R₂`, precisely the type of `c.hom`.
The claimed `c.inv : R₂ ⟶ R₁` has the opposite source and target. Swapping the adjunction order makes `c.inv` an eligible input, but then its inverse conjugate has type `L₁ ⟶ L₂`, namely `b.inv`, not `b.hom`. This is an explicit type failure, visible already with two arbitrary named right-adjoint functors, without any geometric restriction.

Corrected the statement to say that `b` is conjugate to `c`, or equivalently that `b^{-1}` is conjugate to `c^{-1}`. Its source, target, coefficient category, and hypotheses are unchanged. The final bullet of the current unit says only to deduce the pullback isomorphism by uniqueness of left adjoints, so this correction follows that route. The reference master's formula at Defs.lean:300-303 confirms the intent: it inverse-conjugates `lowerStarComp.symm` and then takes another `.symm`. The imported statement omitted that last inversion from its description of the mate. The analogous finite-sheaf imported definition has the same wording issue; it was read for duplicate checking and was not edited.

The only other DAG node referencing this item is `sk-def-sfb-module-pushforward-pullback`; its final bullet and proof require the displayed `h^* ≅ f^* g^*` and uniqueness of adjoints, not the erroneous inverse description, so they remain valid. No citer was edited.

## Existing-node and Mathlib searches

Searched the whole DAG for `conjugateIsoEquiv`, `conjugateEquiv`, uniqueness of left adjoints, composition of adjunctions, `0DV0`, `CategoryTheory.Adjunction.comp`, and `CategoryTheory.Adjunction.leftAdjointCompIso`. Ran `tools/blueprint_refs.py search` for `conjugate`, `adjunction`, `composition of adjunctions`, `pullbacks`, and `0DV0`, and its ancestor command for the item. Read the found generic `def-weil-pbc-adjunction-conjugate` and `def-weil-pbc-composite-adjunction` nodes rather than creating replacements. Read `def-sfb-finite-upper-star-comp`, `lem-sf-mate`, and `lem-sc-left-adjoint-composition-iso-associativity`: the first concerns ordinary coefficient-valued sheaves, the second exceptional derived adjunctions, and the third coherence under strict right-composition equalities. None is the present concrete definition. `same_as` is empty.

Every Mathlib query recorded in the node ran through `msearch.py Q21 def-sfb-module-upper-star-comp`; exact query strings and actual hit lists are logged in the sandbox. All services used here responded successfully. The first semantic phrasing found condensed-module results that do not state this item. The second, more general categorical phrasing returned `Adjunction.leftAdjointCompIso`, and Loogle and the directory-scoped grep confirmed it. LeanSearch returned `SheafOfModules.pullbackComp` and `conjugateEquiv_pullbackComp_inv`; their source was read at PullbackContinuous.lean:146-181. Those use a different presentation of sheaves of modules, so no unproved identification with module objects is used. The generic categorical construction applies directly to the item’s own categories and adjunctions instead.

## Not duplicates

No new nodes. The Mathlib machinery already has DAG interfaces and the item itself is its direct specialization.

## Review by Q21

I read the current main-20261015 chapter `_section.md`, the full `sk-def-sfb-module-pushforward-pullback/_section.md`, and `def-sfb-module-upper-star-comp.md`, together with the imported node. The chapter is about pro-etale coefficient categories. The unit explicitly permits a general commutative condensed ring, constructs the module-object pullbacks and pushforwards, supplies their adjunction, and deduces this comparison from pushforward composition by uniqueness. Nothing in this comparison requires finite coefficients, constructibility, finite type, or invertibility of the coefficient comparison. The corresponding generated chapter/unit JSON records do not exist in this repository snapshot; I used their actual current blueprint texts and did not invent maintainer-owned metadata or change a unit.

I opened all five statements retained as statement dependencies. `def-sfb-module-upper-star` supplies exactly the module-object pullback from Mod over Λ_Y to Mod over Λ_X, including its extension-of-scalars construction; it is not being used to claim a composition theorem. `def-sfb-module-upper-lower-adjunction` explicitly states that this pullback is left adjoint to the specified module pushforward; it supplies a_f, a_g and a_h by application to the three scheme morphisms. `def-sfb-module-lower-star-comp` explicitly supplies c with domain g_* f_* and codomain h_*, and identifies its underlying sheaf map. No proof of that node or its monoidal lifting is borrowed here. `def-weil-pbc-composite-adjunction` explicitly supplies H∘F ⊣ G∘I with the composite Hom bijection, unit and counit; it gives a_{g,f}. Finally `def-weil-pbc-adjunction-conjugate` explicitly supplies the bijection with the reversed adjoint direction, its preservation of identities and composition, the isomorphism equivalence, and inversion compatibility. This validates both the existence and the uniqueness asserted in the corrected definition. These are statement dependencies of a definition; no geometric proof route of another unit is substituted.

For the Mathlib match I read CompositionIso.lean:55-86, Mates.lean:258-309 and :423-435, and Basic.lean:559-582 in the pinned checkout. I also read Stacks categories.tex, Tag 0DV0 (`lemma-compose-counits`, at line 3576), and Tag 0B65 (`lemma-transformation-between-functors-and-adjoints`, at line 3542). They confirm the composite-adjunction order and reversal of directions. The match is exact up to one inversion: set C₀ = Mod over Λ_Z, C₁ = Mod over Λ_Y, C₂ = Mod over Λ_X, and pass a_g, a_f, a_h and c to `Adjunction.leftAdjointCompIso`; its inverse has the displayed type. Diagrammatic Lean composition `g^* ⋙ f^*` is ordinary `f^* ∘ g^*`, while `f_* ⋙ g_*` is ordinary `g_* ∘ f_*`. No ring-sheaf/module-object equivalence, extra instance about pullbacks, or extra geometric hypothesis is needed. The declaration's body itself is the conjugation formula, and `conjugateEquiv_leftAdjointCompIso_inv` at :82 explicitly gives the required mate equation. Bijectivity gives uniqueness, and inversion compatibility gives the equivalent inverse equation.

There are no proof steps in the delivered node because the entire definition is a Mathlib leaf, as required for one-line specializations. For clarity the complete underlying construction has three operations, all covered by the five statements just read: compose a_g with a_f; take c from module pushforward composition; inverse-conjugate c with adjunction order (a_{g,f}, a_h). Equivalently use the inverse of Mathlib's `leftAdjointCompIso`. There is no uncited non-elementary intermediate lemma and no new node restating a clause of the item. `citations.json` is consequently empty rather than fabricating step quotations.

I tested the directions on the case of three identity functors with the same identity adjunction and c the identity: both b and its inverse are identities. This normalized case alone would conceal the imported type error, so I separately checked the types with distinct named right-adjoint functors, as above. The abstract Mathlib types also allow empty categories, the zero coefficient ring (hence its zero-module category), and arbitrary scheme morphisms; no nonemptiness, nonzero-ring, or finiteness condition was used. I do not assume identity scheme maps have strictly identity project adjunctions: the construction uses the given adjunctions and produces the corresponding canonical comparison.

The substantive correction was the mate direction. I also removed the imported paragraph proof because the corrected definition is a Mathlib specialization, filled `same_as`, recorded all actual searches, and added the two existing generic definition dependencies that the precise construction uses. B1-B8 introduce no new-node obligations here; B9 is met by the blueprint search and references, and B10 found no attachment. For C1-C4 and D1-D5 the direct Mathlib formula and the inspected dependency statements cover every operation; there is no hidden lemma, relabelling node, or cycle through the parent unit. E1-E6 were checked by the parameter substitution and direction tests; E7 is the explicit source correction above. No SGA source was used.

## Unfinished work

None in the stage-1 item. The module-object functors, their adjunctions and pushforward composition remain the existing dependencies' work; this leaf does not assert those imported nodes are proved. The sandbox is for the independent second reader; no delivery is authorized from this worker turn.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against `def-sfb-module-upper-star-comp.md` in blueprint `main-20261015`, hypothesis by hypothesis; the schemes, coefficient ring, composite morphism, three adjunctions, pushforward comparison, and displayed pullback isomorphism agree after the explicit mate-direction correction recorded under `## Source error`.
- Item source/proof form: the node is a Mathlib leaf, so it has no proof steps to audit; the construction is the one-line specialization of `CategoryTheory.Adjunction.leftAdjointCompIso` recorded in `mathlib_match`.
- `def-sfb-module-upper-star-comp`: checked B1--B8 (statement-only form, self-contained categories and functors, TeX, source place, and Mathlib declaration/file/line) and B9--B10 (blueprint search and no finished Lean attachment); verdict pass after correcting the conjugation direction.
- Mathlib declaration: read `CompositionIso.lean:72-86`, `Mates.lean:275-435`, and `Basic.lean:567-580`; `leftAdjointCompIso` has type `f^*\circ g^*\cong h^*`, while its inverse has the required `h^*\cong f^*\circ g^*`, and the mate equation is with `c`, not `c^{-1}`.
- Small cases and types: identity functors with identity adjunctions give identity comparisons; distinct named right adjoints expose the imported opposite-direction type mismatch. Empty categories and the zero coefficient ring add no hidden hypothesis.
- Existing-node audit: searched the DAG for the composition/conjugation interfaces and module-object upper-star terminology; the five cited dependency statements provide exactly the constructions used, with no duplicate or restatement node.
- Independent searches: ran the wrapper's grep query `leftAdjointCompIso|conjugateIsoEquiv` on `CategoryTheory/Adjunction` (15 hits) and LeanFinder query “The inverse of the canonical comparison of left adjoint composites is conjugate to the right adjoint composition isomorphism” (8 hits). The latter returned `conjugateEquiv_leftAdjointCompIso_inv` first; read the pinned declaration at CompositionIso.lean:82-86. Both actual query results are appended to the node's search records and the sandbox log.
- Source audit: read Stacks Tags 0DV0 and 0B65 in `categories.tex`; they confirm composite adjunction order and reversal of mate directions. No SGA source was used.

Changes made: retained the worker's explicit `STATEMENT-DISPUTED` correction from “conjugate to the inverse” to “conjugate to `c` (equivalently, inverse to inverse)”; retained the direct Mathlib leaf; appended independent Mathlib search records and this second-reading audit. Corrected an inversion typo in this audit before delivery. The mathematical statement, Mathlib match and empty citations required no further changes.

## Second reading by Q21

- Item `def-sfb-module-upper-star-comp`: checked the corrected statement hypothesis by hypothesis against the blueprint node and the reference construction in `ModuleObject/UpperLowerStar/Defs.lean:300–303`; verdict pass after retaining the explicit mate-direction correction. The commutative condensed ring, scheme morphisms, composite, module-object categories, adjunctions, pushforward comparison, and pullback isomorphism all match the source intent.
- Proof steps: none, because the item is a Mathlib leaf; the one-line specialization was checked against `CategoryTheory.Adjunction.leftAdjointCompIso` (`CompositionIso.lean:72–86`), `conjugateIsoEquiv` (`Mates.lean:425–435`), and `Adjunction.comp` (`Basic.lean:567–580`). The inverse of `leftAdjointCompIso` has the displayed type, and its conjugate is exactly `c` by `conjugateEquiv_leftAdjointCompIso_inv`; verdict pass.
- New nodes: none. The five statement dependencies were opened and checked for the supplied pullback, three adjunctions, pushforward composition, composite adjunction, and conjugation interface; no duplicate, special-case, or restatement node is present. Verdict pass.
- Mathlib and existing-node searches: reran/inspected the recorded grep, LeanFinder, LeanSearch, and Loogle results; the declaration and file/line metadata are exact, and no finished slopmaster2 declaration or reusable DAG node states this concrete module-object comparison. Verdict pass.
- Edge cases and types: identity functors with identity adjunctions give the identity comparison; distinct named right adjoints expose the imported opposite-direction type; empty categories and the zero coefficient ring introduce no extra hypothesis. Verdict pass.
- Changes made: added this required second-reading section only. The corrected mate direction, Mathlib leaf metadata, search log, and empty citations were already accurate; no node or citation changes were needed.
