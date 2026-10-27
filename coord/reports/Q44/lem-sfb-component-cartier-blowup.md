## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-component-cartier-blowup.json: existing statement, split into nine steps; no Mathlib match for the whole construction.
- citations.json: 32 verbatim statement quotations, covering every citation in the nine steps.
- report.md: worker report and signed self-review.

There are zero new nodes and zero new Mathlib leaves. The item statement, statement dependencies, inherited blueprint provenance and source are unchanged. The sandbox initially held only dispatcher brief markers, so there was no earlier proof or report to replace.

## Attachments

None. Searches in lean/WeilConjectures for the blueprint id, blowup and Cartier/component terminology found no declaration stating the whole item. In particular the existing blowup Principalization.lean proves the principalization input, not this entire component enumeration and proper birational construction. Reused its existing DAG theorem rather than adding a declaration or node.

## WANTED

None. Read ILO, Expose X, 2.3 Step 1, printed p.150 (PDF p.156); all Stacks inputs are locally available.

## Findings and corrections

The imported statement is valid; no STATEMENT-DISPUTED correction is necessary. The initial node had no proof. The proof now supplies the missing reasoning that a nowhere dense closed subset of a Noetherian reducible scheme contains no irreducible component: each component contains the nonempty open obtained by deleting the other finitely many components. This matters before applying integrality of blowups, whose ideal must be nonzero.

I checked both the unit/chapter records and the current main-20261015 section and direct-image proof. The node is on an added alteration-input branch with blueprint.from.node null, as confirmed by blueprint_refs ancestor; its inherited from.place describes the component and blowup reductions in the parent. No imported blueprint node states the whole item. Blueprint searches for blowup, Cartier, irreducible components, component Cartier and reduced components were read; the existing Nagata and sfb results supply the inputs. No chapter or unit route is altered.

The current Mathlib searches ran through msearch.py and are in searches.jsonl: two different semantic phrasings with LeanFinder, a Loogle type-pattern search, a grep of AlgebraicGeometry, and LeanSearch. Hits concern normalization or the elementary integral-scheme predicate, not blowups or the full component construction. The inherited search records are retained. No node was created for a constituent already in the DAG or for an elementary subargument.

## Unfinished work

None within stage 1. No Lean was written and no compiler, Lake or build was invoked.

## Not duplicates

No new nodes were introduced. In particular lem-sfb-integral-blowup-projective-geometry is cited for its integral blowup assertion; thm-nagata-global-blowup-proper for properness; thm-nagata-global-blowup-complement for the preserved open; and thm-nagata-blowup-principalizes-center for the Cartier ideal. The existing lem-sfb-integral-blowup-chart-density was read as part of checking the integrality input but its proof is not used as an extra unstated premise.

## Review by Q44

I read the item against ILO X 2.3 Step 1 on printed p.150. That source reduces to components and blows up the marking before normalization; the split treats precisely those reductions, without assuming the components are disjoint, normal, geometrically integral, or curves. I also read the local Stacks proofs: schemes.tex 01J3/01J4 for the reduced induced closed structure; properties.tex 01ON for reduced plus irreducible, 01OZ and 0BA8 for Noetherian topology/components; morphisms.tex 01T6, 01W3 and 01W5; topology.tex 0052 and 04ZA; divisors.tex 02ND, 02NS and 02OS. There are no new nodes needing independent source checks.

For each proof citation I opened the cited node's statement, rather than borrowing a construction from its proof. citations.json quotes those statements verbatim. The checks by step were:

1. The Noetherian-ring definition makes a field Noetherian because all its ideals are 0 or the unit ideal; pqf-def-locnoeth supplies the affine-cover definition. lem-weil-pbc-finite-type-over-noetherian applies to the given finite-type structure map to Spec(e); its hypothesis on the base is explicitly established. lem-weil-pbc-noetherian-finite-components gives finiteness, and lem-sc-irreducible-components-cover gives the covering used to infer a nonempty finite enumeration. These are exactly their assertions.
2. lem-weil-pbc-reduced-induced-closed-subscheme gives the quasi-coherent radical ideal and reduced closed subscheme for each closed component, and separately for its marking. def-pc-integral-scheme explicitly equates nonempty reduced irreducible with integral. lem-weil-pbc-closed-immersion-proper includes the proper-over-base conclusion, not just closedness. Proper entails finite type by def-weil-proper-morphism, so the already cited Noetherian permanence applies to each component.
3. The definition of irreducible component gives closedness, irreducibility and maximality. The finite-union argument is written out, including the one-component case where the union of the other components is empty. This is an elementary consequence of the definitions, not an uncited theorem about dense open subsets meeting components. No disjointness of the components is assumed.
4. lem-weil-pbc-noetherian-open-subscheme-noetherian explicitly asserts quasi-compactness of every open, so it applies to U_i. The Noetherian affine-cover and ring definitions give finite generation on that cover. lem-weil-pbc-quasi-coherent-finite-type-affine explicitly allows passage from finite generation on an affine cover to finite type. The ideal-zero-set-affine node identifies the vanishing set with the marking and shows that a zero ideal would have full vanishing set. Thus the nonzero hypothesis required in step 5 is verified, including an empty marking, where the ideal is the nonzero unit ideal.
5. lem-sfb-integral-blowup-projective-geometry states integrality of the ordinary glued blowup under precisely integral base and nonzero finite-type quasi-coherent ideal; I use only that clause. I do not infer properness from its projective-bundle assertion: thm-nagata-global-blowup-proper explicitly supplies properness. thm-nagata-global-blowup-complement supplies the isomorphism over U_i. A nonempty open in an irreducible scheme is dense by the explicit two-open argument. The integral predicate includes nonemptiness.
6. The definition of proper includes universal closedness, hence closedness without further base change. The image contains U_i by the step-5 isomorphism, so it is all of T_i; this proves surjectivity in the cited definition. lem-weil-pbc-proper-composition applies to the two proved proper morphisms. Finite type of the composite follows from the definition of proper. Thus this step does not hide a projective-to-proper comparison theorem.
7. lem-sc-scheme-sober gives unique generic points. lem-sc-rational-functions-generic-stalks explicitly says every dense open contains the generic points and that the integral generic stalk is a field. def-sc-function-field includes the general integral-scheme meaning, not merely the curve case. The open isomorphism identifies generic stalks; the cofinal neighbourhood argument is written out, so the function-field isomorphism is more than an assertion that birational maps preserve function fields.
8. thm-nagata-blowup-principalizes-center states exactly local generation of the extended ideal by a non-zero-divisor. Its finite-type and quasi-coherence hypotheses were established in step 4. The extended-ideal definition identifies the ideal with the base-change closed subscheme, and lem-pc-closed-subscheme-base-change-ideal-image supplies the image-of-pullback formula. The affine ideal-zero-set statement and the elementary equivalence J B contained in q iff J contained in its inverse image prove the support assertion. This does not claim the exceptional divisor is reduced.
9. The reduced-induced ideal is defined by pointwise vanishing; on the empty set that is the unit ideal. The global complement theorem then applies to the entire base and identifies the blowup canonically with the identity. The word identity in the original statement has this usual canonical-isomorphism meaning, rather than literal equality of a glued construction with its base.

I tested the edge cases T = Spec(e), C empty; a finite disjoint union of field spectra with empty marking; intersecting irreducible components with a proper closed marking at their intersection; and a Cartier marking, whose blowup is already an isomorphism. The forbidden case C containing a whole component would have nonempty interior and therefore violates the item's nowhere-density assumption. The excluded empty T explains why s must be positive. None of these cases needs a stronger hypothesis. All steps are under 700 characters, so no long step hides a separate lemma. Existing citation dependency paths were traversed to check that none returns to this item. Off-unit inputs are basic scheme tools and declared in split_report.tool_uses where needed; no new tool_uses maintainer field was set.
