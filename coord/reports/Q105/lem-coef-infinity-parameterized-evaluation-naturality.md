## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-parameterized-evaluation-naturality.json`: statement, now split into seven steps; no Mathlib match.
- `citations.json`: verbatim statement evidence for every citation in every proof step.
- No new nodes; no Mathlib leaves. The sandbox also contains the actual `searches.jsonl` and the item-local preparation script.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` for the exact blueprint id and for coherent natural transformations/evaluation. No declaration of this full-space quasicategorical assertion was found. The ordinary categorical naturality declarations and 2-truncated homotopy-category declarations are not attachments. The item has no recorded slopmaster2 declaration to audit.

## Sources and WANTED

WANTED: archival copy of Kerodon Definition 5.6.6.1 (038A), Notation 8.3.1.2 (03M4), and Subsection 4.6.8 (01PF), for this item. I read these three pages online. They specify the action/evaluation conventions and the composition law, rather than asserting the entire parameterized result verbatim. Accordingly `proof_origin.by` is `agent`. No Stacks theorem states this quasicategorical assertion, and these are Kerodon identifiers, not Stacks tags. No SGA source is used.

I read the chapter and unit records, and the current main-20261015 blueprint `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, specifically paragraph 2 beginning “For K” and its derived mapping-complex adjunction. This item is a supporting descendant of that blueprint node, not a key statement realizing its unit; no unit record needs changing. The immediate parent's step 4 needs naturality on the entire transformation/arrow family; its small-model transport step needs the same calculation. The proof retains this route and does not invoke Yoneda to establish the naturality needed by Yoneda.

## What was wrong or missing

The item was a statement-only extraction, with no proof or proof dependencies. Its statement is unchanged. The ambiguity of ordinary notation such as G(f)(alpha_a(eta)) is resolved by using the stipulated point-family equivalence throughout, as the statement requires. I did not silently identify an enriched mapping complex with a right-pinched complex.

A tempting general comparison, `lem-coef-coherent-nerve-comparison`, reaches this item through model-colimit-localization, small-diagram rectification, and pointwise Yoneda, so I rejected that citation. The existing `lem-coef-point-family-q-counit-identification` supplies the precise full-family comparison and has no path to this item. Its statement, not its proof, is used. No new node merely restates the item's naturality claim.

## Mathlib and duplication searches

The copied item already contained six searches dated 2026-10-17; I retained them without claiming to have run them myself. I ran and read the six additional queries in the sandbox `searches.jsonl`: two LeanFinder phrasings, Loogle, LeanSearch, and two grep queries. Each added `mathlib_searches` record contains the exact query and the actual log record. Both online semantic services returned successful results. No unavailable service is recorded as an absence.

I read `Mathlib/AlgebraicTopology/SimplicialSet/HomotopyCat.lean:386-406,509-512`, the candidate `mkNatTrans`, its component lemma, and `hoFunctor₂_naturality`; these construct ordinary natural transformations from a 2-truncated homotopy category. I also read `Quasicategory/TwoTruncated.lean:76-110`: HomotopicL/R concern individual edges and do not retain the entire transformation space or arbitrary parameters. The `StrictSegal.lean` naturality hits are operators of an ordinary simplicial object. None is an exact match or one-line specialization of the item.

Whole-DAG keyword searches found the existing point-family-q-counit-identification, point-cocone-criterion, pinch-comparison, mapping-composition, and composition-spine interfaces, which are reused. `blueprint_refs.py search` for “parameterized evaluation”, “point-family”, and “naturality square” found no blueprint node stating this lemma; `same_as` remains empty and the existing precise `from.place` and full ancestry are retained. No new nodes mean there are no new/existing same-tag pairs requiring a Not duplicates table.

## Review by Q105

I checked the actual statement and all seven proof steps with the cited node statements open. The three Kerodon pages above give the correct interpretation: 038A applies the functor to the full morphism space and then evaluates at the given point; 03M4 evaluates a transformation and composes with that point. Neither page assumes the action map is invertible for its definition. The additional naturality is proved here by the universal square, rather than attributed to those definitions.

Step 1 uses kan-coherent-nerve-quasicategory for the target being a quasicategory; enhanced-functor-cone-calculus states that its internal functor object is a quasicategory; pinch-comparison therefore applies to both source and functor categories. The point-family-q-counit-identification statement explicitly supplies beta, its homotopy inverse, compatibility with enriched composition and precomposition by a point, arbitrary additional parameters, and enlargement of universes. I checked that the parameter T need not be W-small: everything auxiliary is formed in the containing universe, while F(a), F(x), G(a), G(x) are the original W-small Kan complexes. I use no colimit indexed by T.

Step 2 is elementary from the internal functor definition and the specified pinch map, not an invocation of a naturality theorem being proved. I checked each of the four corner restrictions of Q and each side: bottom F(j), right alpha_x, left alpha_a, top G(j). The evaluation formula on an n-simplex uses the diagonal parameter in C times Delta^n, so commutation with simplicial operators follows by actual precomposition. The two coordinates u and v are kept distinct.

Step 3 uses mapping-composition's actual statement about V, theta, ell and the characterized composition class. The first triangle has vertices A,B,B'; the second A,A',B'. Both long edges are the same diagonal d. Applying the homotopy-inverse equation for theta to the entire maps h_i:P->V gives the two displayed equalities of maps out of P. This is stronger than checking triangles only at parameter vertices and does not use an ordinary homotopy-category naturality theorem in place of full mapping spaces.

Step 4 uses precisely the point-family-q-counit-identification statement's full composition comparison. The enriched representatives have the correct domains and codomains, so s composed with p and q composed with r are both P->Fun(F(a),G(x)). Cancelling beta is valid because it is a simplicial homotopy equivalence. Postcomposition with evaluation at eta has target G(x), giving the desired type of homotopy-class equation.

Step 5 uses that same node's explicit constant-diagram/point clause together with the point-cocone-criterion's statement that its equivalence identifies a family of maps from the point with the corresponding family of points, including all simplicial parameters. Thus p(-)(eta) is the point map of the actual bottom-side cocone stipulated by the item. The argument never borrows a comparison from a cited node's proof, and never substitutes the rigidification action on a different mapping complex. The right and top sides have exactly the two maps asserted by the item.

Step 6 uses kan-functor-space-kan with K=P and Z=G(x), both in a containing universe. This covers arbitrary simplicial P, with no Kan requirement on P. The horn arguments to reverse and compose finitely many edges are written out, so the conclusion is a single simplicial cylinder homotopy rather than just equality in the homotopy category.

Step 7 keeps the original simplicial square and triangles as the higher witness. I checked the literal restriction formula for B_0->T, and the equation for sigma delta on a simplex of C. These are actual equalities before passing to homotopy classes. Composition-spine states face/degeneracy and higher composition coherence, and point-family-q-counit-identification states retention of all additional simplicial parameters. Those statements support the claimed higher compatibilities; no independent choice of transformations for parameter vertices is made. A compressed homotopy is chosen on the full P once and subsequently restricted for B_0.

I checked hypotheses at every use: C is a quasicategory, the target is the coherent nerve of Kan complexes, the functor object is a quasicategory before using its pinch comparison, and each point/evaluation composite has its declared endpoint. I tested M_x empty (P empty, unique homotopy), T empty, C a point with identity arrow (unit homotopy), a discrete C with x distinct from a (empty arrow family), ordinary nerves with discrete values (the calculation reduces to the ordinary naturality equality), and noninvertible action maps such as a map from a one-point space to a two-point discrete space on C=N([1]). No representability or action-equivalence hypothesis appears, and the last example confirms none is needed. No new statements require separate small-case tests.

I checked delivery-errors B–E: self-contained statement and correct definitions, single TeX escaping, no new unsearched/duplicate/elementary/clause-restatement nodes, every non-elementary input cited, no circular comparison or use of a cited proof instead of its statement, correct arrow orientations and universe hypotheses. The three generic tools from unit sk-prop-sf-cbc are declared individually in split_report.tool_uses with their reason. All seven steps are shorter than 2000 characters (968, 946, 967, 987, 880, 798, 1305), so none hides a lemma in a long step. The citations file records actual verbatim passages. No live repository or Lean source was written and no compiler was run.

## Unfinished work

None for this one-level split. Existing dependencies retain their own independent stage-1 work. Delivery verification follows below.

## Resumption verification

The required first dry run completed with exit 0 and `OK (not pushed)` at temporary commit `32de91a40e`. The additional server `check_dag` also completed with exit 0 and no finding introduced by this sandbox. Neither command pushed a delivery.

On resumption I compared the sandbox item with the current shared item: its statement, source, statement dependencies, chapter/unit, creation record and blueprint ancestry agree; the shared item remains unsplit. I reopened all eleven statement/definition dependencies, the chapter and unit records, the main-20261015 ancestor statement and proof, and the three Kerodon pages. The web gateway returned HTTP 429, so I read those same public Kerodon pages directly with Python urllib without storing files outside the sandbox. The action convention in 038A and evaluation convention in 03M4 agree with Steps 4–5; 01PF constructs composition by inverse spine restriction, as used on the two parameterized triangles in Step 3. I independently rechecked the horn reversal/composition argument of Step 6 and the literal precomposition identities of Step 7. The coherent witness in the last step consists of the original evaluation square and its simplex restrictions; it does not assert that arbitrary horn-filling choices are strictly natural in x.

I repeated the project-source attachment search by the exact id and coherent/parameterized evaluation terminology; it yielded no exact declaration. I read the previously logged Mathlib candidate declarations and retained the original search records without issuing duplicate searches. I checked every citations.json quote against the current cited statement. For Step 3 I expanded the quote to include the actual composition characterization, rather than just the assertion that theta is a homotopy equivalence. The report source path now includes the actual blueprint/ directory. No proof or statement change, new node, or new Mathlib search was needed.
