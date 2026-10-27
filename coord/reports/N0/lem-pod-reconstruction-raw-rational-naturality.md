## Files written

- `dag/nodes/sec-six-functors/lem-pod-reconstruction-raw-rational-naturality.json`: statement item, split into six proof steps; not a Mathlib leaf.
- `citations.json`: 25 verbatim statement excerpts, one for every step/node citation.
- No new DAG nodes and no Mathlib leaves. Search outputs and `searches.jsonl` are retained in the sandbox.

## Attachments

None. I searched the live `lean/WeilConjectures/` by the exact blueprint tag and by reconstruction, completion, raw rationalization and naturality. The affine coherent-formal-module reconstruction declarations concern a different category. `AlgebraicGeometry.Etale.DerivedCategory.rationalization_transport` in `SixFunctors/Etale/Derived/RationalStage.lean:200` is a generic transport result on small etale derived-complete categories. It does not state this item's pro-etale reconstruction, actual unit, identity compact-support comparison and completed scalar equation. It is not an attachment for the whole item.

## WANTED

None.

## Corrections and scope

The item was unsplit, with no proof. Its statement is unchanged; there is no statement dispute. I filled its proof, proof dependencies, proof origin and split report, retaining its source, existing searches, blueprint ancestry and other fields. I read the chapter/unit route and the current main-20261015 proof of `lem-pod-point-dualizing-complex`; this split expands its first sentence about identity compact support, below the unit route. The ancestor is `lem-pod-point-dualizing-complex`, via `lem-pod-identity-compact-support-normalization`.

The proof is explicitly agent-written. Bhatt-Scholze, Definitions 3.5.2-3.5.3 and Lemma 3.5.7, explains the reduction/limit reconstruction; I read the source PDF text at printed pages 24-25, including the regular-ideal condition for unbounded reconstruction. Lemma 6.8.2(1), printed pages 58-59, identifies the completed coefficient sheaf. These are background, not a claim that the paper states this precise raw rational descent theorem. All non-elementary applications in the proof cite DAG statements, rather than the background document alone. There are no SGA citations.

The potentially difficult linearity claim requires no new node: specialize the existing completed scalar-extension theorem to equal fields and equal uniformizers. Its quotient-system functor is the very same reduction tower and its clause (3) supplies ambient linearity. Natural strict Roos comparison identifies the entire derived functors, so this argument does not infer equality of maps merely from their level projections. For restriction to the constructible category I use the actual unit equivalence and invariance of its defining conditions under isomorphism. For scalar extension between distinct fields I additionally cite its constructibility theorem.

## Not duplicates

No new nodes. DAG title/statement searches found `lem-pur-semilinear-scalar-localization`, which already supplies generic descent of transformations, whiskering and equations. It is reused. Whole-blueprint searches for rationalization, reconstruction, identity compact support and semilinear scalar found no blueprint statement equivalent to the complete item; `blueprint.same_as` remains empty. The parent normalization lemma depends on this item and is not cited back.

## Review by N0

I read delivery-errors B-E in full and reviewed the six steps against the actual statements in the live DAG, not their proofs. There is no prior sandbox split, report or search log to reuse; the inherited searches in the live node were preserved. Five additional searches were genuinely run through `msearch.py` and their complete outputs were read and recorded. The second LeanFinder phrasing tests the normalized-system interpretation. The hits provide ordinary module completion, generic derived linearity, or unrelated sheaf functors, not the actual project comparisons. No unavailable service was labeled as a negative match.

Step 1 uses the explicit equal-field tower and clause (3) of `lem-weil-integral-scalar-extension-well-defined`; the equality case is permitted by its subfield hypotheses. `lem-coef-derived-system-evaluation-calculus` specifies the reduction functor and total limit on precisely the same module/system universes. I checked that `lem-weil-strict-roos-comparison` covers unbounded strict towers and maps, and discharged its exact-products assumption with `lem-weil-proetale-countable-products-exact`. `lem-weil-integral-constructible-linear` explicitly supplies ambient bilinear composition, so conjugation by the natural comparison preserves linearity. There is no assertion that arbitrary choices of a cone give a natural functor.

Step 2 uses the actual-unit isomorphism asserted by `lem-pur-normalized-reconstruction-adjunction-calculus` for complete objects, without adding finite-Tor or site-perfectness. `lem-trf-completion-unit-strict-quotient-model` identifies that unit as an entire derived arrow. The definition `def-weil-derived-complete-integral-detailed` states completeness and uniform bounds on all reductions; these are invariant under an isomorphism. The inverse-naturality equation is written by multiplying the unit square by inverses; it is not an additional uncited theorem.

Step 3 opens the definitions of finite compact support, extension by zero and derived direct image. For the identity compactification the sheaf functors are literally identity under their canonical identifications; localization inverts the resolution maps. I also read `lem-sf-compact-support-restriction-of-scalars`: its comparison is built from the underlying extension-by-zero identification and derived direct-image comparison. With both geometric maps identity these are the identity coefficient comparison. `lem-weil-compact-support-reduction-tower-functor` gives all the transitions and morphisms, rather than only the level objects. Thus taking its total limit in `def-weil-integral-rational-qbar-compact-support` identifies the actual tower with reconstruction before rationalizing. This is a direct substitution in the stated constructions, not a new independent lemma or a use of the parent proof.

Step 4 applies `lem-pur-semilinear-scalar-localization` only after establishing linearity and closure in steps 1-2. The localization and rationalization definitions supply the Hom tensor groups and bilinear composition. I verified balancing and preservation of composition on tensor generators. Step 5 uses the same lemma's transformation and inverse clauses; the two displayed calculations check naturality on every finite tensor sum. This covers torsion in integral Hom groups: only the balanced tensor relations are used, with no cancellation or injectivity assumption on localization.

Step 6 uses integral scalar-extension linearity and `lem-weil-integral-scalar-extension-constructible` to check the source and target are the stated full categories. `lem-pod-completion-unit-scalar-intertwining` states naturality of the specified comparison and exactly the inverse-unit square used here, including ramified extensions. Its actual map is retained. The coefficient homomorphism sends the nonzero uniformizer of E to a unit in the field L, so all hypotheses of semilinear localization hold; no assumption that the two uniformizers coincide is made for unequal fields. The rationalization definition gives the displayed functorial equality on integral arrows, and tensor-linearity extends the naturality squares to arbitrary rational arrows.

For small cases I checked the zero object, zero arrows and empty tensor sums, identity arrows, a tensor killed by localization, and equal fields with the same uniformizer. None requires faithful localization. Ramification only enters through the already specified integral comparison and the nonzero element of L; there is no integral lift of a rational isomorphism. All objects remain integral-category objects; no idempotents are adjoined. I checked dependency reachability for the generic tools to exclude a cycle through this item, and declared generic off-unit tool uses in `split_report.tool_uses` for the maintainer to assess. Every proof step is shorter than 1000 characters, so none crosses the 2000-character review threshold. B's new-node shape and same-tag pair checks are vacuous because no nodes were created. C1/C4 were checked with the opened statements and `citations.json`; D's relabeling fault is avoided by proving the tensor formulas and reusing strictly more general existing tools; E's object, universe, completeness, constructibility and scalar hypotheses were checked above.

## Unfinished work

None in this one-level stage-1 split. Existing cited unsplit or unproved dependencies remain their owners' tasks. No Lean source was written and no compiler, Lake or build tool was run.
