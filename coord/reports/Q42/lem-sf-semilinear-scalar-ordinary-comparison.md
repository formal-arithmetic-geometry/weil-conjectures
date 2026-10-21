## Files written

- dag/nodes/sec-six-functors/lem-sf-semilinear-scalar-ordinary-comparison.json: statement, split; no full Mathlib match. Eleven proof steps using existing nodes. The statement and its four original statement dependencies are unchanged.
- citations.json: 28 verbatim statement excerpts for every step/node pair.
- searches.jsonl: six actual searches made with msearch.py; the item's pre-existing search history is also retained in its JSON.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: this is a subsidiary node, not the unit's key statement.

## Attachments

None. I searched lean/WeilConjectures for the blueprint tag, semilinear terminology, scalar comparison terminology, and relevant file names. EtaleRestrictScalarsFunctorComparisons.lean contains AlgebraicGeometry.Etale.lowerStarRestrictScalarsIso and upperStarRestrictScalarsIsoSheaf, but these concern fixed-ring sheaves on the small etale site. They do not state this item about arbitrary semilinear pro-etale systems, open extension, the clopen projector and intrinsic ordinary alpha. Consequently they are neither an attachment nor a substitute for this split. Existing Sheaf declarations recorded on the cited varying-ring definition nodes are not claimed as closed proofs of this item.

## Wanted literature

None. All sources used in the proof are present. The current chapter/unit DAG records point to main-20261017; the proof text actually available and read for the blueprint ancestor is literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md. The current unit's complete statement and step were also read from dag/units/sk-thm-sf-compatibility.json. This item realizes their coefficient/unit-counit sentence and does not alter their route.

## What was wrong or incomplete

The item had no proof. The single source pointer to 03D7 was insufficient to document its sheafification and localized open-extension clauses. The new proof records the additional precise sources at each step and marks the assembly as agent-written. Its assertion itself is correct: scalar restriction is being used, not extension, and no flatness is necessary. There is no statement dispute or source correction.

The proof deliberately remains ordinary: equality is checked on components of actual module-sheaf system maps. No faithfulness of derived evaluation, no preservation of K-injectives and no derived direct-image comparison is used. I did not cite the parent lem-sf-semilinear-proper-open-mate-pasting: that would make the argument circular.

The original Mathlib search history is retained. The new six searches all ran and their hits were read. The second LeanFinder phrasing found sheafification Hom-equivalence and underlying-presheaf declarations; the first found fixed-ring and scheme-module restriction functors. I read Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean, Presheaf/ChangeOfRings.lean, Presheaf/Pushforward.lean and Sheaf/PullbackContinuous.lean. These construct the ingredients, not the entire statement including semilinear transitions and the intrinsic alpha word. Therefore the item is not a Mathlib leaf. No absent search is asserted; all six services/commands returned successfully. Generic facts already available in the DAG suffice, so no new lemma is manufactured for a short scalar-action or adjunction calculation.

## What remains unfinished

Nothing in the stage-1 split. Lean formalization and proofs are outside this assignment. Delivery validation and push are run after writing this report; their results are recorded below when available.

## Not duplicates

No new nodes. Existing definitions and generic results are cited rather than recreated. Blueprint searches for restriction scalars, semilinear, 03D2 and 03DI found no blueprint node stating the whole item. The 03DI blueprint result is the existing extension-by-zero construction; the split uses its already available more explicit localized module formulation. The supplied item's nearest ancestor is fix-prop-coherence, confirmed by blueprint_refs.py ancestor. Its original from.place and via chain are retained and same_as is the searched empty list.

## Review by Q42

I read coord/delivery-errors.md B through E in full and checked each step against the statements of all its cited nodes, rather than relying on their titles or proofs. I also read the relevant Stacks text: sites-modules.tex, 03D2 (lemma-pullback-module), 03D3 (lemma-adjoint-push-pull-modules), 03D6 (definition-pushforward), 03D7 (lemma-adjoint-pullback-pushforward-modules), the 03DA kernel/cokernel construction, and 03DI (lemma-extension-by-zero). The action-uniqueness formulation of 03CY and the localized 03DI/03DJ adjunction are stated explicitly in the cited existing nodes. No SGA source is used. There are no new nodes requiring separate source reviews.

1. For the construction of rho, def-pc-sheaf-restrict-scalars really says the underlying abelian sheaf is unchanged. lem-coef-semilinear-derived-sections states the source category with semilinear transitions, and lem-cbc-strict-tower-proper-open-calculus defines the constant-B target. I checked the crucial equation c_n(phi_{n+1}(b)) = phi_n(b); it gives B-linearity of every transition. Presheaf restrictions satisfy the same equation for local constant-ring sections. Maps, identities and composition use their original section maps. This is a short calculation, not a new node.

2. For sheafification, def-weil-presheaf-modules-sheafification states both the unchanged abelian sheafification and uniqueness of the extending action. Therefore the two B-actions on that common abelian sheaf are equal. This justifies commutation with sheafification without incorrectly claiming that a universal-property-only sheafification definition provides a plus construction. def-pc-sheaf-restrict-scalars supplies the presheaf action being extended.

3. The kernel and cokernel formulas are actually in def-weil-sheaf-of-modules-category. Combined with step 2, these prove exactness at one level. lem-coef-semilinear-derived-sections explicitly provides componentwise exactness and applies also to the constant ring sequence B. Thus exactness of rho follows without assuming flatness, finite coefficients or exactness of sections.

4. def-sp-varying-ring-operations specifies the section value M_n(H times_Y X) and unchanged transitions of direct image. def-weil-pbc-proetale-operations supplies its scalar action, and the constant tower lemma identifies the comparison target. I checked that the two actions use the same constant-sheaf coefficient map and that the identity section maps respect transitions and restrictions. This supplies the requested normalization, not just an unspecified natural isomorphism.

5. For inverse image I used the levelwise inverse-image assertion in lem-coef-semilinear-derived-sections, together with the concrete transported-action formula in def-weil-pbc-proetale-operations. This latter node states more than the bare name of inverse image: it specifies L(mu), the finite-product comparison, and the isomorphism m tensor r maps to c^{-1}(r)m. Applying L to the composite action equals composing L(mu) with L(phi). This is the required B-linearity calculation. Naturality in the transition maps lets these level comparisons form a system map. The unit-preserving evaluation statement in def-sp-varying-ring-operations identifies it with the specified system pullback. No arbitrary choice of a left adjoint is silently identified with the given one.

6. I checked both unit and counit equations with their domains. The concrete ordinary module adjunction in def-weil-pbc-proetale-operations restricts the underlying abelian adjunction, and def-sp-varying-ring-operations specifies the ordinary system adjunctions and their unit normalizations. Hence the displayed equations can be tested on ordinary components. def-weil-pbc-adjunction-mate gives exactly the unit--b^{-1}--counit composite. Substitution of the counit equation, naturality of the unit, and the triangle identity give d, with the inverse of b in the correct direction. This rules out the common error of assuming a mate of an isomorphism must automatically be invertible.

7. The varying-ring definition explicitly states the sectionwise direct-image compositor and the unit-preserving inverse-image and open compositors. The constant tower lemma fixes their comparison normalization. Identity on sections preserves fibre-product pasting. After taking adjoints both proposed pullback composition maps have the same transpose, so injectivity of the adjunction bijection gives equality. This is an ordinary adjunction calculation, not a derived coherence claim.

8. lem-pur-site-restriction-module-adjunction-exact explicitly constructs extension by zero by localized direct sums followed by sheafification; def-weil-extension-by-zero-presheaf states all summands, restriction maps and scalar actions. I checked on a summand that restriction keeps its elements and action through phi. Step 2 extends the comparison. At a localized object (H to U), the open unit is the injection indexed by that map; the counit maps a summand G|_U(H to U) = G(H) identically to G(H). Both are unchanged. For compositions of opens, both maps send an iterated summand to the composite-indexed summand. Sheafification uniqueness then proves the compositor equation. Thus normalization of a_j is proved, not presumed from an abstract isomorphism.

9. def-sp-varying-ring-proper-open-arrows actually defines beta inverse by the transpose of the open unit and the inverse-image square compositor. The constant tower lemma states this same transpose and its invertibility. Earlier steps preserve both factors and the summand description of the open-adjunction bijection. The two inverse beta maps therefore have the same transpose, and are equal; their inverses are equal too. I used only this stated definition, not a construction hidden in a node's proof.

10. The constant tower lemma supplies the geometric clopen lift for the exact proper/quasi-compact-open hypotheses of the item; it requires no cartesian hypothesis on the original square. The varying-ring arrows definition supplies the unit-defined s_! to s_* map, its clopen invertibility, and pi_s. The same preserved adjunction word gives the same projector, also described in the constant-tower statement as identity and zero on the two components. I checked the full-open case gives the identity and the empty-open case gives zero.

11. Both cited proper/open statements explicitly contain the alpha word: beta, then the whiskered clopen projection, then open/pullback compositors. The preceding steps preserve each factor. Applying functoriality to their composite proves exactly the ordinary alpha clause. No separate node restates that clause and no parent theorem is invoked.

I tested zero module systems, zero coefficient rings where compatible unital maps exist, nonflat maps such as Z to Z/2, constant ring systems with identity transitions, identity scheme maps, empty/full opens, and a noncartesian square whose lift selects one of two clopen components. The actions, direct-image identities and unit equations still have their stated types; the projector is identity on the selected component and zero on the other. No step assumes cartesianness of systems, surjectivity of the coefficient maps, boundedness, or finite coefficients. The longest step is 1199 characters; none crosses the 2000-character review threshold or hides a comparison lemma left unproved. All generic off-unit tools are listed in split_report.tool_uses with the precise part of their statements used; no accepted tool_uses field is set by this delivery.

The final written files retain the imported statement, creation metadata and blueprint chain. Citations were constructed from actual statement substrings, with an assertion for every excerpt; their purpose is to witness the exact input at each step, and the prose above explains the remaining explicit calculations. B (form/search/duplicates), C (statements and complete citations), D (proof carried by steps, not renamed clauses), and E (hypotheses and actual maps) were all checked against the written proof.

## Delivery validation

The first completed dry-run diagnostics required longer verbatim excerpts for three citation witnesses (steps 4, 5 and 10); their statements did support the uses, but the excerpts were below the 40-character minimum. I expanded them to the full relevant formulas/sentences and also made five other excerpts more specific. Every excerpt was rechecked as a contiguous part of its node statement. No proof or statement change was needed.

Server dry run exited successfully: OK (not pushed) at ff14f9a1d7c, preflight passed. In the final source review I sharpened the wording of step 8 to give the open unit at every localized object and the precise identity-on-each-summand counit, rather than an informal restriction description. This uses the same already-cited formulas and changes no dependencies or statement. The final tree is dry-run again before pushing.
