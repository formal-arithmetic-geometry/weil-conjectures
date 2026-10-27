# Stage-1 report: lem-pur-compact-support-strict-scalar-refinement

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-compact-support-strict-scalar-refinement.json: existing statement split into eleven proof steps; no new nodes; not a Mathlib leaf.
- citations.json: 35 verbatim excerpts, one for every node cited by every proof step.
- report.md: this report. searches.jsonl is the unmodified search-command record.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, strict towers, refinement/coefficient combinations and compact-support scalar terminology. I read SixFunctors/ProEtale/FiniteCoefficient/Derived/ExtendScalars/LowerShriekBaseChange.lean, especially rightDerivedLowerShriekOfCompactificationBaseChange_extendScalars_app. That theorem concerns fixed-coefficient derived sheaf categories and a cartesian open exchange square. It does not state this item's equality in the ordinary derived category of integral strict reduction towers, or its noncartesian refinement normalization. It is not an attachment for the item. No Lean file was written or compiled.

## WANTED

None. The argument is explicitly agent-written; no numbered Stacks theorem is claimed to state this whole strict scalar-refinement assertion.

## What changed and why

The existing statement is retained verbatim, including its strict-tower category, ramified indices, clopen projection, inverse direction of the refinement comparison, bounded-below finite etale-origin domain and total-limit normalization. Its seeded source and all original Mathlib search records are retained. The empty proof is replaced by a genuine calculation: the scalar/open pullback cube, its clopen projection component, its proper mates and the outer proper pushforward, followed by inversion in the specified direction. No new node merely restates the square.

I read the original returned Step 8 in coord/reports/Q13/lem-pur-compact-support-integral-coefficient-comparison.md and expanded its short assertion that tensor preserves the projection and mate pasting gives the result. I read main-20261015 thm-pur-rational-and-qbar-purity.proof.md Step 2 and sk-thm-purity-transport/_section.md, and the current recorded unit sk-thm-sf-compatibility, especially its coefficient clause. This item realizes a detail below that clause and does not change the unit or chapter route; it is not the unit's key statement and no unit record is edited.

I also searched the whole DAG for the named facts, Stacks Tags 0F7B, 0F7C and 0F7D and clopen/tensor terminology, and ran blueprint_refs.py searches for clopen, strict scalar, proper open, scalar, compactification and coefficient comparison. The nearest blueprint ancestor remains thm-pur-rational-and-qbar-purity, with the inherited intermediate nodes. No imported blueprint statement asserts the complete strict scalar-refinement square in another form. The existing generic nodes below supply the ingredients; no duplicate is created.

## Mathlib searches

I ran the required msearch.py command with the item id, using two LeanFinder phrasings, LeanSearch, Loogle and grep; read their output; then ran a targeted logged grep for the mate composition declarations. The new records are copied from searches.jsonl exactly, retaining the tool and query strings and actual hit summaries. All services answered successfully. The semantic hits concern condensed/profinite topology, ordinary inverse systems and module completion, not this derived strict-tower compact-support comparison. Loogle found CategoryTheory.mateEquiv_vcomp and mateEquiv_hcomp; logged grep located them at Mathlib/CategoryTheory/Adjunction/Mates.lean:170 and :209, and I read their full statements and proofs. They are already represented by lem-weil-pbc-mate-pasting, so I cite that existing Mathlib leaf instead of creating one. The entire item is not a one-line specialization of those formulas, since its open clopen-projection cube and normalized compactification construction must first be proved.

## Review by Q64

I checked delivery-errors B through E against the actual statements and sources. There are no new nodes, so no unsplit proof sketches, missing definition records, Mathlib leaves without lines or same-tag new-node pairs. I retained all statement dependencies because the unchanged statement explicitly names them. The proof dependencies equal exactly the union of the step citations. All eleven steps are under 2000 characters. The substantive work is in Steps 4-7, rather than deferred to a new copy of the desired assertion.

I read more-etale.tex at lemma-shriek-proper-and-open (Tag 0F7B), its vertical composition lemma (0F7C), and its horizontal composition lemma (0F7D). The source is the finite etale result, and does not itself assert the pro-etale strict-tower scalar cube: that portion is written here and uses the already-stated strict calculus. I read sites-modules.tex lemma-j-shriek-and-tensor (0E8I), sites-cohomology.tex lemma-adjoint (07A6), and lemma-derived-limit-is-ok (0941). These fix the relevant open tensor, adjunction and total-limit background. I read the complete statements of all nineteen proof dependencies, not only their titles or proofs. The following checks identify exactly what each step takes.

1. I checked lem-pur-compact-support-coefficient-models against the same E subset F, separated finite-type f and finite-Tor M as this item. It gives compatible finite bases, the constant/completed comparisons, and bounded constructibility of C_X M. def-weil-derived-complete-integral-detailed requires bounded constructible reductions. Clause (ii) of lem-sf-proetale-constructible-origin really gives bounded complex etale-origin witnesses, not just origin of individual sheaves. lem-weil-compact-support-reduction-tower-functor supplies strict lifts, evaluated morphisms and all-pair quotient transitions. Thus the hypothesis used by the strict proper/open calculus is supplied separately at every finite level, also at retained F-levels en. The proof never invokes an unjustified uniform bound.

2. I checked quasi-compactness of the opens, which the imported statement did not explicitly repeat. lemma-nagata-open-immersion-qc-over-separated-target assumes a quasi-compact composite and a quasi-separated second map. Here the composite is f and the second map is the proper compactification map. lem-pc-separated-quasi-separated supplies the latter condition. The proper/open calculus then supplies the clopen lift, actual identity/zero projection and its proper mate, for arbitrary constant coefficient rings including infinite A and B. Its finite-witness hypotheses from Step 1 give invertibility. I did not replace the original refinement square by a cartesian square: its pullback factorization contains the extra clopen section.

3. The finite basis from the coefficient-model node identifies the underlying tensor with a finite direct sum. The levelwise abelian and exact assertion of lem-weil-tower-category-levelwise-abelian justifies exactness on strict systems, so ordinary tensor is the needed derived functor. lem-sf-open-tensor-normalization explicitly includes ringed diagram topoi with arbitrary transitions; its open map and pulled-back unit normalize b_j. The named strict scalar-mate node supplies the actual diagram-category proper mate and its ordered proper/open composite, not just its evaluation. This rules out an unjustified strictification from isolated degreewise equalities.

4. I checked the inverse-beta formula against the statement of lem-cbc-strict-tower-proper-open-calculus and the open-unit formula against lem-sf-open-tensor-normalization. They say that inverse beta is the transpose of the pulled-back unit and that the unit is identity on open summands. Both candidate scalar extensions send x tensor b to the same summand. Uniqueness of the adjunction transpose then proves the square and inversion yields the beta version. It is a short identity of the cited normalized maps, marked elementary, not a claim of a new general comparison theorem.

5. The calculus literally defines pi_s as identity on s(V) and zero on its complementary open component. Both tensor composites send ((x,y) tensor b) to (x tensor b,0), a balanced B-linear formula. Open tensor normalization identifies these with the specified b maps. This is a sheaf-map identity on complexes of strict towers, so it commutes with both differentials and every transition; it is not inferred from faithfulness of derived evaluations. I checked the displayed cube's source G_p,B T_Z i_!,A and target k_!,B T_V G_r,A. No flatness of quotient transitions is used.

6. I read clauses (1) and (2) of lem-weil-pbc-mate-pasting and the source Mathlib formulas at lines 170 and 209. They give the two ways of pasting mates and the correct composite-adjunction unit/counit. The two faces supplied in Step 5 therefore have the displayed proper mates. I checked that their source is T_Z i_!,A R_r,A and target R_p,B k_!,B T_V. The explicit counit definition of a_u is the one in lem-pur-compact-support-strict-scalar-mate, and the explicit eta/alpha/epsilon definition of gamma is in the strict calculus statement. Thus the citations actually supply the normalization used, including the order of proper and open maps.

7. I substituted r = identity, p = u, k = j_c, i = j_d into Step 6, then used the same mate-pasting lemma for the exterior proper map p_d. Its composition-adjunction clause identifies the composite scalar mate with a_p_c. The scalar-mate statement identifies q with precisely R_p(b_j) followed after a_p, on the diagram category. The strict reduction-tower statement supplies its evaluated separately derived images and quotient transitions. The equation initially obtained has Theta from d to c; this direction is intentionally retained until the next step.

8. lem-cbc-complete-proetale-refinement-exchange-coherence states C_u = R_p_d gamma from F_d to F_c and that it is invertible on precisely the finite-witness domain already checked. Here C_u is Theta. I multiplied the established equality by the inverse on both sides, obtaining rho = Theta inverse in the question's c-to-d direction. Tensor and subsequence restriction are functors, so they preserve inverses. This is elementary cancellation in the same derived tower category.

9. The same refinement-coherence node actually states identity, reverse-order composition, independent common-refinement comparisons and their cocycle. The strict proper/open calculus states the vertical and horizontal composition equations for arbitrary commutative proper/open squares and identifies the intrinsic alpha with the pasted one. The mate-pasting node supplies the corresponding proper compositor normalization. prop-compactification-refinement really gives cofilteredness, including equalization of parallel arrows, under the item's finite-type field hypotheses. Pasting Step 8 along both common-refinement arrows therefore gives choice independence and the cocycle; it does not postulate a preferred common refinement.

10. I checked the exact-products premise of the Roos results using lem-weil-proetale-countable-products-exact, whose statement allows arbitrary coefficient ring sheaves. lem-sf-strict-roos-derived-limit-comparison gives the K-injective/Roos realization for arbitrary strict tower complexes with this premise. lem-pur-compact-support-roos-cofinality gives the actual block restriction and tensor/product maps, their naturality, cofinal isomorphism, and augmentation preservation. The step writes the two naturality equations and substitutes them, so its transport of the square is an explicit functorial calculation, not equality deduced from reductions. Ramification e only changes the subsequence and its block transition maps.

11. I checked that lem-weil-pbc-constant-completion-equivalence states not only an equivalence of complete objects, but the compatibility of finite reductions, quotient transitions, derived limits and completion units. The coefficient-model node fixes the ordinary/strict scalar comparison. The compact-support definition actually defines its integral value by the reduction total limit; def-sf-refinement-comparison-isomorphism specifies the inverse proper/open map followed with the proper compositor. The strict calculus asserts exactly that finite normalization. Thus the final transport identifies the specified total-limit construction and maps, without asserting that evaluation or finite reductions are faithful.

The two existing off-unit ingredients most distant from this compatibility unit are common refinements and the constant/completed equivalence. They are used only as generic tools, not to replace the unit's coefficient route. The server's review_split check accepted the route as it stands. No top-level tool_uses approval was added by the worker.

I tested small cases: M = 0 and X empty give zero maps throughout; E = F and e = 1 give the identity coefficient square and identity subsequence restriction; an identity refinement has s = identity, so the projection is the identity. A refinement whose pullback has a nonempty complementary open component gives projection (x,y) to (x,0), and tensor keeps exactly that zero component. This specifically checks the normalization that would be lost by treating the refinement square as cartesian. For ramified e > 1 all arguments occur on strict maps and preserve composite transitions before the block-map comparison. None requires quotient-transition flatness, smoothness or purity. There is no statement dispute and no source error identified.

## Not duplicates

No new nodes. Existing generic mate-pasting, open tensor normalization, strict proper/open calculus, refinement coherence, finite coefficient models and normalized Roos comparison are reused.

## Unfinished work

None in the requested one-level split. The existing unsplit coefficient-model and strict scalar-mate nodes remain dependencies in accordance with the stage-1 contract; they are not claimed proved or split here. No Lean or later-stage work was attempted.

## Validation

The required server review_split check passed with zero new nodes. The unit has no realization recorded yet; this is an advisory on the shared unit record, and this auxiliary item is not authorized to edit it. Full dry-run and push results follow from the delivery command output.

The full dry run caught an overly short Step 8 citation excerpt. I replaced it with the full refinement-map definition and isomorphism passage from the cited statement, retaining a verbatim quote.
