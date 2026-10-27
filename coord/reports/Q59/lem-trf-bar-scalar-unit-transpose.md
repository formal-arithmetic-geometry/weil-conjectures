# Q59: lem-trf-bar-scalar-unit-transpose

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-bar-scalar-unit-transpose.json`: statement, split in six proof steps; Mathlib searches found no exact or one-line generalization. The statement is unchanged. No new nodes and no Mathlib leaves.
- `citations.json`: a verbatim statement quote for every dependency of every proof step.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint id and for bar/scalar and colimit/change-of-ring expressions. There is no project declaration giving the full chain comparison together with its representative-normalized transpose and common-unit equation. Ordinary coefficient adjunction declarations do not supply this item.

## WANTED

None. The relevant Stacks sources are present locally.

## What needed repair

The item was unsplit. Its source is expressly an agent extraction, so I have marked the expanded proof as agent-written. I kept all existing provenance and prior search records, and appended only searches actually run through msearch.py. The searches returned ordinary tensor/restriction units, generic adjunction formulas, group bar complexes and Dold-Kan comparisons; none supplies the small-category derived-colimit claim. I read the unit/hom-equivalence and colimit-preservation source in Mathlib's `Algebra/Category/ModuleCat/ChangeOfRings.lean`, the unit-equation equivalences in `CategoryTheory/Adjunction/Basic.lean`, and the group complex in `RepresentationTheory/Homological/GroupHomology/Basic.lean`. In particular, a group-resolution comparison does not specialize in one line to arbitrary categories with arbitrary module-valued coefficients.

The existing statement already corrects the order and adjoint direction in Stacks 08Q8: both composites go from R-presheaf derived objects to D(S), and both are LEFT adjoints to restriction followed by constants. I did not propagate the ill-typed printed order or the printed claim that these are right adjoints. This is an inherited source correction, not a new change to the statement. No use of SGA.

## Not duplicates

No new nodes. Whole-DAG searches for the category-bar unit, colimit unit, scalar comparison and Stacks evaluation-to-derived label were read. Whole-blueprint searches for `bar`, `colimit unit`, `derived colimit`, `derived adjunction`, and `evaluation` do not give an imported node stating this item. The existing coefficient-change node is the parent using this item; the scalar-coherence node is a different coherence assertion and is not used here. The augmented bar and reindexing lemmas are existing infrastructure, not reasons to create more bar nodes. I also read those statements to check the meaning of the canonical bar representatives.

## Unfinished work

None in this split. The maintainer independently reviews the delivered argument.

## Review by Q59

I read `sites-cohomology.tex` at Tags 08PG (example-left-derived-colimits), 08PH (example-morphism-categories), and 08Q8 (lemma-change-of-rings), including the actual bar differential and semilinear generator formula. I also read the derived lower-shriek adjunction at 07AC, the representative derivation of adjunctions in `derived.tex` at the labels lemma-pre-derived-adjoint-functors and lemma-derived-adjoint-functors, and `categories.tex` at Tags 0B65 and 0DV0. The imported blueprint ancestor and the chapter/unit records were read: this is a generic coefficient-comparison input on the already recorded semistable/cotangent branch, not a change in that route. The six steps realize the finite-sum and unit-transposition part explicitly named by the item's blueprint.from.place.

For step 1 I opened and read the full statements of lem-trf-derived-colimit-bar and lem-pur-sheaf-ring-derived-coefficient-adjunction. The former gives the precise bar objects and the canonical semilinear chain map. The latter explicitly gives the units x maps to x tensor 1 on K-flat representatives with flat terms. I checked those hypotheses separately for F[0] on the presheaf site and K_R(F) on the point site: both are assumptions of the item, so no flatness of S over R has been inserted.

Step 2 is the tensor universal-property calculation, written on finite-support sums. The displayed forward map respects the R-balancing relation, the inverse is additive and balanced before descending through the tensor quotient, and both compositions fix spanning generators. No unmentioned tensor/direct-sum theorem is being assumed. This is an elementary step, not a separate node. Step 3 cites the actual differential clause of lem-trf-derived-colimit-bar, and checks both kinds of faces, including the coefficient restriction in the last face. The alternating signs agree, hence the inverse is a chain map too; this proves the derived isomorphism by localization of an actual chain isomorphism.

Step 4 uses precisely clause (2) of lem-pur-sheaf-ring-derived-coefficient-adjunction, whose statement computes the adjunct of a chain map from the given K-flat source. I checked the source is K_R(F), not an unjustifiably flat K_S(H) over R. The formula z tensor s maps to s g(z) gives the inverse in step 2, in the direction B(F) to A(F).

In step 5 the word canonical matters: the canonical semilinear derived-colimit map of lem-trf-derived-colimit-bar is the transpose of the coefficient map followed by the target colimit unit. I wrote that map and its source/target, rather than inferring a derived unit equation just from degree-zero generators. The bar theorem is cited for that canonical map and its representative, not for an invented extra chain-level unit formula. The two adjunction transposes give the displayed equality; def-pc-sheaf-restrict-scalars identifies the exact same underlying constant complexes, and def-weil-pbc-composite-adjunction gives precisely the two composite-unit formulas. I opened and read these statements. This step does not assume restriction is full or that point evaluations detect equality of derived presheaf morphisms.

Step 6 cites lem-weil-pbc-conjugate-iso-unit-equation for the global natural comparison and def-weil-pbc-composite-adjunction for its Hom bijection. I checked the direction by setting L_1=B and L_2=A. The injectivity of that Hom bijection identifies the single component beta_F once the unit equation is known; it does not assume explicit tensor representatives for every derived object. These four off-unit inputs are declared as generic tools in split_report.tool_uses.

I checked delivery-errors B--E against the files: no statement-only node with a hidden proof, no new clause moved out of the item, no new duplicates, no missing non-elementary input, and no cycle introduced through the parent coefficient-change lemma. All steps are shorter than 2000 characters. The small cases are the empty category (all bar terms zero), a singleton category (the same formulas on the unnormalized bar), F=0, S=0, and the identity ring map (the usual unit normalization); the balancing and face checks still apply. A nonflat test R=Z, S=Z/2, F constant Z is allowed and does not change the calculation. Naturalness and common-unit uniqueness use the whole derived categories; only the explicit component requires the two K-flat hypotheses. Every citation quote was checked verbatim against the current cited statement.
