# Q142: fixed Cohen presentation and lifted evaluation square

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-cohen-presentation-lifted-evaluation-square.json`: statement; split using existing nodes, no Mathlib match for the entire statement.
- `citations.json`: seven verbatim statement quotations, one for every step/node pair.
- `searches.jsonl`: five actual searches for this item, including two semantic phrasings; results read and recorded in the item. `write_split.py` is sandbox-only preparation material.

No new nodes and no new Mathlib leaves. The item's statement, statement dependencies, source, and existing search history were retained.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for Cohen/presentation/lifting terminology. No project declaration states the entire fixed-source square with its arbitrary specified kernel tuple and evaluation congruence. The private `MvPowerSeries.local_lift_of_formally_smooth` in `CohenPowerSeriesParameterExtension.lean:36` proves a general lifting subargument, not the item. The public parameter-extension and complete-local-map presentation declarations have different data and conclusions. The evaluation declaration `MvPowerSeries.exists_unique_adic_evaluation` in `PowerSeriesAdicEvaluation.lean:52` is already represented by the existing evaluation node; it does not prove the whole item.

## WANTED

None. All sources needed here are available locally.

## What required repair

The item was unsplit, with no earlier sandbox proof or report. Its statement is sound and was not changed. Stacks 09PZ omits details of the subsequent surjectivity argument; this item explicitly stops before that assertion. Its actual content is supplied without assuming a surjective evaluation map, a residue-field identification for the coefficient ring, or regularity of R. The source's Q versus Z distinction is handled by the existing field/Cohen formal-smoothness node, whose statement supplies the Z formulation in both cases.

The newest blueprint unit and ancestor were read in `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`. They address local terms; the assigned item is an algebraic descendant of the previously introduced complete-local comparison. This delivery keeps that assigned descendant's source route and does not change the chapter, unit, ancestor statements, or their realization records. Blueprint searches for `Cohen`, `07NJ`, and `power series`, together with the whole-DAG search, found no blueprint node stating this item. The existing algebraic nodes are reused as generic tools, declared in `split_report.tool_uses`.

## Not duplicates

No new nodes were created. Existing DAG statements for field/Cohen regular complete power-series rings, field/Cohen adic formal smoothness, complete-target lifting, and adic evaluation already cover the non-elementary inputs. In particular no new node restates the lifting clause or the evaluation clause of the item.

## Review by Q142

I read Stacks `dpa.tex`, Tag 09PZ (`lemma-ci-well-defined`), especially the fixed-source first paragraph and the third paragraph constructing the lift and displayed square. I also read `more-algebra.tex`, Tags 07NJ (`lemma-lift-continuous`) and 07NL (`lemma-power-series-ring-over-Cohen-fs`), and the power-series substitution paragraph of 07NN (`lemma-embed-map-Noetherian-complete-local-rings`); `algebra.tex`, Tag 032C (`remark-Noetherian-complete-local-ring-universally-catenary`), confirms the field/Cohen regular-complete structure theorem. There are no new-node sources to review. No SGA source is used.

Step 1 cites the coefficient-family definition of multivariate power series. Its finite Cauchy-product formula proves the regrouping isomorphism directly: the coefficient at each pair of multi-indices is the same finite sum in either ring. The projection and its constant-series section are written explicitly. This avoids introducing a node for a rearrangement of indices.

Step 2 cites `lem-weil-pbc-power-series-field-cohen-regular-complete`; I read its full statement, which gives the exact maximal ideals, completeness, and regular locality for every number of variables, including zero. Both applications have the required field or Cohen coefficient ring. Locality of the projection then follows on the displayed ideal generators.

Step 3 cites the definition of adic completeness, which explicitly includes separatedness. I checked that the kernel is inside the source maximal ideal because the target is a nonzero local ring, and that an element in every J + m_R^N maps into every m_A^N. Thus the closed-kernel hypothesis is proved from separatedness of A; neither J-adic completeness nor an unproved assertion that every ideal is closed is used. The quotient identification is explicitly the bijection [u] maps to r(u).

Step 4 cites both `lem-weil-pbc-field-cohen-power-series-formally-smooth` and `lem-weil-pbc-fs-adic-lift-into-complete`. I opened both statements: the first supplies formal smoothness over Z for both allowed coefficient cases; the second supplies a lift and the exact ideal-image bound. I matched its source S with T0, target A with our R, its closed ideal with ker(r), and its ideal I with m_R. Both integer exponents are one. The condition g(m_T0) contained in q(I) is verified using surjectivity and the elementary fact that a unit has unit image: each lift of an element of m_A lies in m_R. The lifting conclusion therefore gives locality itself, not merely continuity. No residue-field isomorphism of Lambda with A is assumed.

Step 5 cites `lem-weil-pbc-power-series-adic-evaluation`. Its full statement gives existence, restriction on coefficients, prescribed variable values, and exactly the total-degree congruence requested here. The target R is complete at m_R and every b_j lies in that ideal by step 3. Locality of h is checked using the already proved maximal-ideal description and locality of f; it is not inferred from mere continuity. I read the corresponding project declaration to confirm that the truncation is by total degree.

Step 6 cites adic completeness for separatedness. The actual commuting calculation is written out: applying r kills every positive-degree monomial in the b_j and sends the error ideal into m_A^N, so separatedness gives equality for each series. This uses no unjustified uniqueness among arbitrary discontinuous maps. The case s = 0 reduces to h = f and pi = identity; n = 0 reduces to the same lifting theorem with source Lambda. I also checked J = 0, redundant or zero kernel generators, N = 1, the field case with zero coefficient maximal ideal, and the Cohen case with coefficient maximal ideal p Lambda. The construction works in each case.

Against delivery-errors B–E: no new statement-only nodes, no new unsupported notions, no invented searches, no duplicate or clause-restatement nodes, no use of a cited proof instead of its statement, no undeclared non-elementary input, and no change of coefficient categories. All seven citations are verbatim copies of the cited statements. No proof step exceeds 2000 characters (the longest is 810), and the elementary steps are coefficient rearrangement, the separatedness calculation for the kernel, and the separatedness calculation for the square. No compiler or Lake command was run, and no repository or launcher file was written.

## What remains unfinished

Nothing in this stage-1 split. Future formalization remains the project's later-stage work. Server `check_dag` and `review_split` passed before this report; the required delivery dry run and push follow.
