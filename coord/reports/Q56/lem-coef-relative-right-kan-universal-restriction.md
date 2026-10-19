# Stage-1 split: lem-coef-relative-right-kan-universal-restriction

## Files written

- `dag/nodes/sec-six-functors/lem-coef-relative-right-kan-universal-restriction.json`: existing statement, now split in ten steps; unchanged statement and statement dependencies; no Mathlib match.
- `citations.json`: 35 entries, one for every step/node citation, with verbatim statement fragments.
- `report.md`: this worker report.

## New nodes

None. Zero new nodes and zero Mathlib leaves. All 17 proof dependencies already exist. In particular, the local parameter argument is written in steps 2–3 from existing boundary and cone-corner lemmas; it is not hidden in a new lemma that restates the item.

## Attachments

None. I searched the item tag and the notions relative/right Kan extension and quasicategory in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` (also Comparator) and checked the upstream-master reference search. The hits in ordinary derived-functor/site files use ordinary category Kan extensions; none states the relative quasicategorical assertion, much less all its clauses. The existing item has no recorded project declaration. I wrote no Lean and ran no compiler, Lake or build command.

## WANTED

WANTED: Lurie, *Higher Topos Theory*, Lemmas 4.3.2.7 and 4.3.2.10–13, Proposition 4.3.2.15 and Remark 4.3.2.18, printed pp.274–285, for lem-coef-relative-right-kan-universal-restriction. I read the official Harvard PDF online; no archival download was made.

WANTED: archival Kerodon Proposition 7.3.6.7 (030F), Proposition 7.3.5.5 (0302), Corollary 7.1.5.17 (02WS), Propositions 7.1.6.13 (02XB), 7.1.6.19 (02X1), 7.1.8.7 (06A5) and 7.1.8.10 (02XK), for lem-coef-relative-right-kan-universal-restriction. I read these online. These identifiers are Kerodon tags, not Stacks tags. No Stacks theorem supplies this quasicategorical result. The proof is therefore marked `proof_origin.by = agent`, with exact online places and an explicit argument.

## What was wrong or missing

The imported item was a statement-only tool with no proof. Its statement is correct and remains byte-for-byte unchanged; there is no STATEMENT-DISPUTED and no added hypothesis. The cone clause includes exact base and boundary equations, so an argument merely comparing cones up to equivalence would have been incomplete. Steps 7–9 now perform the two necessary equivalence lifts explicitly.

The older `lem-coef-relative-right-kan-restriction` assumes that every boundary functor is extendible, whereas this item uses the full subcategory T of locally extendible functors. I did not apply the older node without its hypothesis. Likewise `lem-coef-infinity-kan-mapping-restriction` is absolute, and `lem-coef-infinity-parameter-cone-extension` only provides the absolute universal-cone hypothesis. Neither was silently treated as relative. The relative parameter calculation and relative mapping square are proved in the item instead.

The unit and chapter records were read but not changed. I checked the inherited ancestor's paragraph 2 both in the older master file and in the current main-20261015 separate proof file under `sk-thm-sf-package`: the derived mapping-complex comparison before the inverse limit is unchanged. This item is a generic foundation for the already accepted operadic Segal/bar branch of that paragraph, not a change in the unit route or coefficient categories. `blueprint.from` is preserved, with the full exact place; `same_as` is `[]`. Whole-blueprint searches for “right Kan” and “relative cone” found no blueprint node stating this tool.

## What remains unfinished

No part of this one-level split remains mathematically unfinished. Existing unsplit dependency nodes remain their owners' work; no new statement-only nodes were needed. The required server checks and no-push dry run are recorded below when completed. A fresh second reader must independently read, repair if needed and deliver; I do not push.

## Not duplicates

No new node is created. Relevant existing near-matches were inspected rather than duplicated: the all-diagrams restriction node has the stronger global-existence assumption, the absolute mapping-restriction node lacks the relative base square, and the absolute parameter-cone-extension node lacks the relative p-limit hypothesis. The relative cone corner, relative-final boundary criterion, local relative Kan existence and constant-source test already provide exactly the smaller facts used in the proof.

## Mathlib searches

All seven added search entries were actually run with `msearch.py Q56 lem-coef-relative-right-kan-universal-restriction`; the original six entries from the item's creation are retained. I used LeanFinder twice with distinct phrasings, LeanSearch, Loogle, and source grep in CategoryTheory/Functor/KanExtension and AlgebraicTopology/Quasicategory. The first Loogle query used an unqualified identifier the service did not recognize; this is recorded as unavailable and was repaired by the quoted fully qualified query, which returned 12 results. None of the searches was fabricated.

I read Mathlib `CategoryTheory/Functor/KanExtension/Basic.lean` at 45–90, `Pointwise.lean` at 780–811, and `AlgebraicTopology/Quasicategory/Basic.lean` at 29–105. The first two use ordinary Category instances and ordinary terminal right extensions; the last has the primitive inner-horn class. Neither gives the relative coherent functor-category restriction or cone comparison. Thus this is not an overlooked Mathlib leaf.

## Review by Q56

I am the author and this is my self-review, not the second reader's review. I read the whole delivery-errors B–E checklist and the actual statement of each node used by each step. The sources for the item were HTT's relative Kan-extension section and Kerodon 030F as listed above. There are no new nodes for which an additional source needs reviewing. I checked the following uses against statements, not against a dependency's proof.

1. Step 1 uses isofibration-exponentiation's corner theorem for the inclusions A in C, simplex boundary in simplex and cone boundary in cone; the theorem expressly allows arbitrary small simplicial monomorphisms. Relative-cone-initial-corner expressly identifies p-limit diagrams with final objects relative to this cone corner and gives its isofibration. Relative-initial-boundary supplies its final boundary test, and enhanced-functor-cone-calculus supplies quasicategory closure and full subcategories. The fixed-base fiber is a quasicategory by pulling back the inner horn problems; no completeness is inferred from exponentiation.

2. Step 2 cites monomorphism-boundary-cells for the skeletal attachment and relative-initial-boundary for the actual fillers. I checked that a missing simplex of the product must cover both factors; therefore its last vertex is the already specified final object at (m,n). This is valid for all m,n positive, including the square m=n=1, whose missing diagonal edge and two triangles have that same final vertex. There is no illicit dimension-zero finality requirement. The equality of the two exponential/cone corners is written as an equality of their three pieces of data, so relative-cone-initial-corner legitimately supplies the conclusion that the family is a P_n-limit. Exponentiation ensures its corner is an inner fibration between quasicategories, as the final criterion requires. This replaces an unsupported appeal to absolute parameterized limits.

3. Step 3 uses exactly the right-hand clause of relative-kan-existence: a full inclusion of small quasicategories, an isofibration P_n, and local limit lifts with exact prescribed base and boundary. At every c the last-parameter cone is H l_c, not a cone merely assumed to be equivalent to it. The one-simplex as well as the higher boundary problems are legitimate because that last vertex is relative-final by the cone-corner node. Step 2 proves local P_n-universality before applying the existence theorem. Relative-initial-boundary then gives V-finality. No statement about arbitrary complete fibers is used.

4. Step 4 uses the actual U-space clause of exponentiation: for an inner fibration, its endpoint-fixed arrow-space map is a Kan fibration. These U spaces commute exactly with pullbacks. Pullback-path-comparison permits a strict pullback to model a homotopy pullback with that fibration leg. The pinch node gives natural equivalences to the stipulated mapping model, and homotopy-pullback-invariance permits that replacement. Relative-initial-boundary's definition of V-finality supplies the remaining mapping equivalence. Thus the relative square for arbitrary F is proved and is not falsely attributed to the absolute Kan-mapping-restriction node.

5. Step 5 obtains only the zero-dimensional lifts from local relative-kan-existence, checking every local cone in T against that theorem. For n positive every vertex is already prescribed on the boundary, so the filler from step 3 lands in the full subcategory R, even though the extension theorem itself works in the larger functor category. Its p-image remains exactly the constant s. The result is exactly the boundary-lifting definition in trivial-kan-fibration, including n=0, not only essential surjectivity.

6. Step 6 uses boundary-cells to pass from boundary lifts to all monomorphisms, the Joyal model node's stated weak factorization system to recognize a trivial fibration, and quasicategory-characterizations(2) to obtain a genuine functor equivalence. I did not infer an infinity-categorical equivalence from an arbitrary weak homotopy equivalence of underlying simplicial sets.

7. Step 7 checks the hypotheses of local relative-kan-existence on A in the left cone of C, not on the non-full union C with the left cone of A. The join is a quasicategory by the explicit inner-horn block argument written in the step, using the join and horn definitions. At c in C there is no arrow back to the apex, so the local index really is L_c; at the new apex its local index is literally A, so the assumed limiting q_A is the required local cone. This is why the existence proof needs q_A limiting, as the item allows. For the separate cone clause I explicitly write s_H=pH, so no extra assumption that this H lies over the initially fixed s is imposed. The initial result q' need not yet have the entire prescribed boundary; the next steps correct this rather than asserting it without proof.

8. Step 8 uses cone-initial-corner and relative-initial-boundary in dimensions 1 and 2 to construct an equivalence over the identity of the complete boundary/base data. Both cones are relative-final, so both inverse triangles are available. Exponentiation lifts this equivalence for A-left-cone in C-left-cone, keeping b fixed; its source is the already constructed q'. Cone-equivalence(1), together with its explicit right-hand dual in (4), preserves the particular local p-limit cones under the resulting natural equivalence. I enlarged the corresponding verbatim citation to include the opposite-duality assertion, rather than quoting only the colimit clause.

9. Step 9 uses the same final-boundary criterion for V to compare H'' to the originally prescribed H over the identity on A and s. These identities are strict, which permits gluing to the identity on q_A over the intersection A. The enhanced functor calculus detects that this glued transformation is an equivalence at every vertex. Exponentiation allows the inclusion of K even though K need not itself be a quasicategory, and produces a cone with all three exact equalities of the item. A source-prescribed lift, not an unsupported target lift, is used at each of the two strictification steps.

10. Step 10 applies the existing constant-source test exactly as stated, with arbitrary z and the actual cone apex x. The right square is step 4 for the constant F, which does not have to be right Kan extended. Right-proper Kan fibrational models turn its homotopy-pullback cancellation into an iterated-pullback calculation; this derives the small pasting fact from a cited model theorem rather than introducing another node. Naturality in restriction in the constant-test statement identifies the outer rectangle with q_A's actual test. Thus both directions hold for every prescribed cone, not only the one constructed in steps 7–9.

I tested the statement and argument at A=C (restriction is the identity and no new local data are needed), C empty (both functor fibers are the unique empty diagram and cone comparison is the identity on the apex), A empty with C nonempty (T either is empty or expresses exactly the needed local relative-final objects), p the identity (all relevant local relative-limit conditions are automatic and strict base data determine the extension), and p to a point (the ordinary infinity-categorical theorem is recovered). Empty T forces empty R, so the map empty-to-empty satisfies all boundary lifting tests vacuously. For cone existence when A is empty, q_A is exactly the local p-limit over the apex's empty boundary; this is not omitted. The m=n=1 parameter test was also checked explicitly. None of these cases requires D or its fibers complete.

For B1–B10: there are no new statements, definitions or leaves; statement and hypotheses are preserved, searches are real, sources are correctly labeled Kerodon rather than Stacks, blueprint ancestry is explicit, and project attachment was ruled out. For C1–C8: the 35 citations have verbatim support; every non-elementary input is in their cited statements; the only off-unit proof tool, enhanced-functor-cone-calculus, is declared in split_report.tool_uses; no unit step is replaced. I also checked that none of the 17 cited proof dependencies reaches the item, so this proof introduces no back edge. For D1–D5: the ten steps contain the parameter, universal mapping and exact cone arguments themselves, with no newly created restatement or circular lemma. For E1–E7: I checked the full-inclusion, size, isofibration, final-vertex, exact-base and fixed-boundary hypotheses at their applications; there is no source error, SGA use, target weakening, or coefficient-category identification.

## Validation

Server-only review_split via the authorized srvcheck wrapper: PASS; 0 new nodes; agent-written proof; declared generic tool use accepted. The required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q56 lem-coef-relative-right-kan-universal-restriction --no-push` completed with exit 0 and printed: `OK (not pushed) deliver/Q56/lem-coef-relative-right-kan-universal-restriction at 12331207ab: preflight passed`. This includes the required server preflight and DAG/review checks. No delivery was pushed. The sandbox is ready for the independent second reader; only this validation-result sentence was updated after that successful run.

## Second reading by Q56

I independently reread the item statement against HTT §4.3.2 (Lemmas 4.3.2.7, 4.3.2.10–13, Proposition 4.3.2.15 and Remark 4.3.2.18, especially printed pp. 274–285) and the cited Kerodon relative Kan-extension/cone results. The right-hand dual, fixed-base equations, full-subcategory hypotheses, and absence of completeness assumptions agree clause by clause; the tests (A=C), (A=\varnothing), (C=\varnothing), (p=\mathrm{id}), (p) terminal, and the (m=n=1) parameter case introduce no counterexample.

1. Step 1: checked the two exponential corners, fixed-base fibers, full-subcategory quasicategories, and cone-corner/final-object criterion against the four cited statements; verdict correct, with only the stated pullback-of-horns elementary argument.
2. Step 2: checked the product boundary-cell filtration, surjectivity-to-the-terminal-vertex argument, and identification of the parameter corner with the cone corner against the boundary-cells, relative-final, cone-corner, and exponentiation statements; verdict correct for every (m,n>0), including (m=n=1).
3. Step 3: checked the local (L_c) boundary data, exact last-parameter cone, application of relative Kan existence, and finality criterion against the three cited nodes; verdict correct and uses no dimension-zero condition (the cited finality criterion explicitly has none).
4. Step 4: checked the arrow-space pullback, Kan-fibration leg, pinch replacement, and mapping-space characterization against all five cited nodes; verdict correct for arbitrary (F), with the actual restriction maps retained.
5. Step 5: checked zero-dimensional existence, positive-dimensional boundary lifting, fixed-base preservation, fullness of (R), and the stated definition of trivial Kan fibration against relative Kan existence and the definition node; verdict correct.
6. Step 6: checked the extension from boundary inclusions through the stated monomorphism filtration and the Joyal weak factorization/equivalence criterion against all three cited nodes; verdict correct.
7. Step 7: checked the join (C^{\triangleleft}) quasicategory argument, the local coslices at (c\in C) and at the apex, and exact application of relative Kan existence against the join/cone definitions and existence node; verdict correct.
8. Step 8: checked relative-final comparison edges, dimension-two inverse triangles, exact lifting through the exponential corner, and invariance under equivalence against the five cited nodes; verdict correct, including the right-hand dual used for limits.
9. Step 9: checked strict identity on (A) and in (B), gluing on (K=C\cup_A A^{\triangleleft}), componentwise equivalence, and the final exact lift against the four cited nodes; verdict correct even though (K) need not be a quasicategory.
10. Step 10: checked the constant-source squares, pasting with Step 4, homotopy-pullback cancellation via right properness, and both directions of the cone test against the two cited nodes; verdict correct.

There are no new nodes or Mathlib leaves to review. I searched the existing DAG for each cited tag and the source tree for relative/right Kan and quasicategory matches; all 17 dependencies already exist and each citation quote matches its node statement. I found no duplicate, cycle, unsupported fact, SGA citation, statement defect, or missing hypothesis. I changed no node, proof step, citation, or search record; this section is the only addition.
