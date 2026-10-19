# Worker report: lem-coef-infinity-cofinality-space-test

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-cofinality-space-test.json`: item, statement; Mathlib verdict no match; split into 11 proof steps using existing nodes only.
- `citations.json`: 23 entries, one for every step/node pair, each quoting the cited statement verbatim.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0. The statement, three statement dependencies, historical blueprint ancestry and unit binding are unchanged. `blueprint.same_as` remains empty after the whole-blueprint searches.

## Attachments

None. Searches for the item's tag and for cofinal/cofinality throughout `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` found no declaration stating the theorem. The unrelated finite-stalk, neighbourhood and finite-type-submodule occurrences do not assert any of its four quasicategorical tests. The corresponding master tag search also found none. Master is reference material, not a finished-proof certificate.

## WANTED

WANTED: archived Kerodon Proposition 7.4.3.11 (04K3), Theorem 7.2.3.1 (02NY) and Remark 7.2.3.2 (02NZ), for lem-coef-infinity-cofinality-space-test. Read online at https://kerodon.net/tag/04K3, https://kerodon.net/tag/02NY and https://kerodon.net/tag/02NZ.

WANTED: archived Kerodon Proposition 7.4.3.6 (05RR) and Example 7.4.3.7 (05RS), for the left-fibration total-space calculation and the corepresentable colimit calculation used by lem-coef-infinity-cofinality-space-test. Read online at https://kerodon.net/tag/05RR and https://kerodon.net/tag/05RS. No Stacks Project theorem states these coherent infinity-category results. These identifiers are Kerodon tags. No SGA source is used.

## Findings and changes

The imported node was true but had no proof. No STATEMENT-DISPUTED correction is needed. Its definition of finality quantifies over diagrams with a specified existing colimit, including targets that have no other colimits; the proof retains this quantifier. Its comma model is the oriented arrow pullback, and the proof works directly with that model, without silently substituting a join slice or a set of objects.

Kerodon 04K3 uses its own right-cofinal notion and regular-cardinal bounds. Rather than create a new node that merely states another one of this item's equivalences, I give a presheaf proof of the difficult converse. In P(B), form W_A = colim_A y_B u and W_B = colim_B y_B. Pointwise colimits give the corepresentable tests. Yoneda identifies maps from these two presheaves to Q with the two limits of Q. Under (4), their actual comparison is an equivalence. This gives the actual restriction of limits, hence preservation of any specified colimit cocone by the mapping-space criterion. Universe enlargement is checked separately: the fixed-universe small-space tests suffice, because the two small-indexed presheaf colimits remain colimits in every containing universe. The presheaf proof is agent-written and is marked accordingly.

For (3) versus (4), the proof writes out the total-space colimit argument from existing transport classification, small Kan replacement and the groupoid-localization universal property. It does not assume a hidden straightening/colimit theorem. For the ordinary-functor clause it identifies every simplex and every operator of the comma nerve.

All newly appended Mathlib search records are searches actually run through the required msearch command for N6 and this item. Two unquoted Loogle inputs reported unknown identifiers; these parsing failures are recorded as such, followed by the successful quoted full-name query. The services were available. The semantic hits and `Final.lean:86-104,476-515` show ordinary Category instances, connected comma categories and Type-valued colimits; these are insufficient for weak contractibility and coherent space-valued colimits. `SSet.hasColimits` is about strict colimits of simplicial sets. No match was promoted to a Mathlib leaf.

## Not duplicates

No new nodes were created. I searched the whole DAG by cofinality, comma categories, weak contractibility, space-valued tests and the source tags, and used `tools/blueprint_refs.py search` for cofinality space, 04K3, cofinal, colimit corepresentable and Quillen. No blueprint node states this theorem. The existing right-adjoint-reindexing theorem has an ordinary adjunction hypothesis; final-index-colimit concerns a final vertex; slice-equivalence-final is a final-object criterion inside a slice; cofinal-kappa-poset is a replacement theorem for filtered quasicategories; grothendieck-aspherical-base-change concerns ordinary categories and weak equivalences of their nerves. None can replace the item. Yoneda and presheaf/transport tools already present were reused.

## What remains unfinished

Nothing in this split. Its existing unsplit prerequisites remain existing DAG work, not new nodes. No Lean file was written and no compiler, Lake or build command was run. Only this sandbox was written. No delivery is pushed; this is the first reader's handoff for the independent second reader.

## Review by N6

I read the stage-1 brief, stages/1-dag.md, the worker role, SETUP.md including the three route levels, the chapter and unit records, GOAL.md, coord/dag-sync.md, and delivery-errors B through E in full. The current main-20261015 ancestor proof is the finite-level R Hom adjunction before R lim. This is foundational work below that proof, not a replacement of its coefficient-duality or finite-adjunction route. I left the maintainer-owned unit binding unchanged. I read the five Kerodon sources named above and compared all hypotheses: A and B are small quasicategories, the space diagrams are coherent, the comma is oriented b -> u(a), weak contractibility includes nonemptiness, and the universal finality assertion requires no global cocompleteness of its target. I also opened the entire statement of each node cited below, rather than relying on a title or on its proof.

Step 1 uses `lem-coef-space-transport-classification`: it explicitly gives the full Kan mapping complex over the base, the constant-product classifier, composition compatibility and small representatives. An over-map E -> I x X is exactly its X-coordinate; this is the elementary degreewise isomorphism written in the step. Classification over a point supplies the mapping-space model for Kan complexes.

Step 2 uses `lem-coef-kan-quillen-right-proper` for its actual functorial model structure and Kan fibrant objects, hence factorization E -> R -> point inside the small simplicial sets. `lem-cbc-simplicial-groupoid-localization` applies because R is Kan and E -> R is a weak homotopy equivalence; since the target X is Kan its full functor category already inverts every edge. It asserts a full equivalence, not a statement only about the ordinary homotopy category. The transport node turns r into the particular cocone and identifies its postcomposition map, and `lem-cbc-enhanced-functor-cone-calculus` states exactly that equivalence of those maps for all X recognizes a colimit. I corrected the draft's loose horn-filling explanation of why the functor sets are Kan: the final step instead uses the explicit Kan over-map-complex clause of transport. Thus no extra pushout-product theorem is hidden there.

Step 3 uses the source-fixed arrow classifier and pullback compatibility explicitly stated in transport. Its total pullback is literally the item's comma simplicial set; I checked the evaluation endpoints and the n-simplex operators. Smallness is preserved by these finite products and subsets. The left-fibration lifting range includes the inner horns, so the total space is a quasicategory after filling the projected horn in A. Applying the already proved total-space calculation is therefore legitimate and proves both directions (3) and (4).

Step 4 uses the explicitly covariant clause of `lem-coef-infinity-pointwise-yoneda-evaluation`, not just full faithfulness of Yoneda. The point-base transport formula identifies Map(*,X) with X. Evaluating the constant transformation at 1_b is the identity on X, also with parameters, so the cited cocone criterion recognizes the canonical cocone to the point. This proves the required corepresentable colimit instead of introducing it as a new clause node.

Step 5 uses `lem-coef-spaces-small-colimits-universe` for both required small colimits and `def-cbc-enhanced-diagrams-cones` for initial cocones. The inverse-comparison argument is elementary from their contractible mapping spaces and proves that the specific canonical comparison is an equivalence. Step 6 is the immediate substitution of the corepresentable diagram into condition (2) and step 4; it needs no additional lemma or citation.

Step 7 uses the existence of small presheaf colimits explicitly stated in `lem-coef-infinity-presheaf-free-cocompletion`, the pointwise criterion explicitly stated in `lem-coef-infinity-yoneda-presheaf-limits`, and transport's coherent bifunctor to define y_B. The cited functor-cone calculus says a transformation is an equivalence iff its components are. I checked the directions W_A -> W_B and y_B: B -> P(B), and that evaluation at b produces a covariant diagram on A, exactly as (4) requires. Both A and B are small in the same original universe, including the empty cases.

Step 8 uses the colimit mapping-space formula from the Yoneda/presheaf-limits node and the full natural evaluation equivalence from `lem-coef-infinity-yoneda-evaluation`. On the a leg the induced map selects the u(a) leg. Thus the map between limits is restriction along u^op, with its coherences, not an unspecified equivalence of limit objects. All limits of spaces used here exist by the limits node. No construction from the proof of the presheaf-free-cocompletion node is cited or used.

Step 9 uses the universe-colimit preservation clause of `lem-coef-spaces-small-colimits-universe`, the pointwise colimit criterion and Yoneda in the larger universe. This is the necessary size check: a target E may have mapping spaces larger than the spaces tested in (2) and (4). The same W_A and W_B remain colimits after inclusion, so (4) is not strengthened to a test for larger diagrams. The original small A and B are the only colimit shapes.

Step 10 uses transport's coherent mapping bifunctor to define Q_T(b) = Map(D(b),T), after enlarging the universe to contain E and its mapping spaces. The colimit criterion in `lem-coef-infinity-yoneda-presheaf-limits` then tests the specified cocone. I checked the leg f lambda_{u(a)} and the contravariance of Q_T. No colimit in E other than the given cocone is invoked. This proves the exact finality quantifier of (1).

Step 11 uses the nerve, internal Fun and degreewise-pullback definitions of `def-cbc-enhanced-diagrams-cones`. A natural transformation [n] x [1] -> J with constant source j and target v(i_-) is exactly a chain in the ordinary comma category, with its commuting equations. Restriction and repetition of that chain give faces and degeneracies, so the identification is of simplicial sets. This checks the final clause without invoking ordinary connected-comma finality.

Small cases checked by hand: if A is empty and B has an object then (4) gives an empty colimit and fails, and (3) has an empty comma and fails; the constant point diagram shows (2) fails. If B is empty then A is empty, conditions (3),(4) are vacuous, and the unique comparisons and reindexing are identities. For u = identity, step 4 gives the corepresentable tests. For a discrete B, (3)/(4) require every discrete fiber to have exactly one object; an omitted point or a doubled fiber fails as it should. For a groupoid-shaped comma the full homotopy type, not just pi_0, is retained by Kan replacement, so a connected noncontractible example is not incorrectly accepted. Empty small-space diagrams are allowed throughout.

Against B-D: no new statement-only node was needed; notions are supplied by the unchanged statement dependencies and the explicitly cited interfaces. The mathematical sources are Kerodon tags, accurately labelled as such; no SGA or false Stacks attribution is used. Every non-elementary input is the statement of an existing cited node. The substantial presheaf argument remains in this item's steps, so neither a clause nor the entire theorem is moved into a new node. I checked that the existing presheaf, transport, localization, Yoneda and cone-calculus dependencies do not reach this item, so the new edges introduce no cycle. The two generic tools from sk-prop-sf-cbc are declared in split_report.tool_uses, not in maintainer-owned tool_uses. `citations.json` was checked against the exact statement strings for every one of its 23 entries. No false or ill-typed source statement, extra hypothesis, missing nullary case, or hidden compatibility assertion was found.

Server review_split passed with 0 new nodes and the declared generic tool uses. The required `python3 /home/ubuntu/weil-launcher-nt/deliver.py N6 lem-coef-infinity-cofinality-space-test --no-push` dry run printed `OK (not pushed)` with preflight passed. Nothing was pushed. The final report was then included in a repeat of the same dry run, so the handoff is the accepted sandbox.

## Second reading by N6

I reopened the item statement against Kerodon Proposition 7.4.3.11 (04K3), Theorem 7.2.3.1 (02NY), and Remark 7.2.3.2 (02NZ): the four clauses, the orientation (b\to u(a)), the weak-contractibility meaning, and the small/containing-universe hypotheses agree; the empty-source and empty-target cases remain included. I checked the five auxiliary source places 05RR and 05RS as well; their left-fibration total-space and corepresentable-colimit assertions match the uses in the proof.

- Step 1: checked against the full transport mapping-space and constant-left-fibration clauses of `lem-coef-space-transport-classification`; the over-map/X-coordinate bijection is elementary.
- Step 2: checked the Kan model factorization, groupoid-localization hypothesis (E\to R), and cocone mapping-space criterion against all four cited statements; no hidden horn or localization input remains.
- Step 3: checked the source-fixed arrow pullback, left-fibration pullback, and exact displayed comma orientation; the inner-horn and smallness claims are elementary from the cited transport statement.
- Step 4: checked covariant Yoneda evaluation at (1_b), the point-base transport formula, and the cocone criterion; the canonical cocone is the one proved colimiting.
- Step 5: checked finality, existence of the two space colimits including the empty diagram, and uniqueness of initial cocones; the canonical comparison is the restricted cocone map.
- Step 6: checked the direct substitution (D=H_B(b,-)) into clause (2) and Step 4; no external fact is used.
- Step 7: checked the presheaf colimit construction, pointwise evaluation, coherent (y_B), comparison direction (W_A\to W_B), and componentwise equivalence criterion against every cited statement.
- Step 8: checked both mapping-space colimit formulas, Yoneda naturality on each colimit leg, and the direction of restriction (\lim_{B^{op}}Q\to\lim_{A^{op}}Qu^{op}); the map is identified coherently, not only up to homotopy type.
- Step 9: checked universe enlargement against the explicit colimit-preservation clause and the pointwise/Yoneda statements; the fixed-universe test is not silently strengthened.
- Step 10: checked the larger-universe mapping presheaf (Q_T(b)=\operatorname{Map}_{\mathcal E}(D(b),T)), its variance, and the specified cocone legs against the mapping-bifunctor and cocone criteria.
- Step 11: checked the degreewise nerve computation from the internal-functor definition; faces and degeneracies identify the comma simplicial set with (N(j\downarrow v)).

There are no new nodes to audit. I searched the DAG for the item, cofinality, comma, weak contractibility, and the cited source tags; the existing cofinality, filtered, and ordinary-category nodes do not state this four-way coherent-space theorem. I also checked the cited dependency statements in full and found no circular edge or tool-use omission. The small tests in the worker report (empty cases, identity, discrete fibers, and noncontractible groupoid fibers) are retained and are consistent with the statement.

I changed the node's `created` metadata from the stale unrelated item/group (`lem-coef-sifted-nerve-index-calculus`, `NH`) to this item and group `N6`; this is required by preflight and does not change the mathematical statement or proof. No statement correction, node addition, Lean file, compiler, Lake, or build action was needed.
