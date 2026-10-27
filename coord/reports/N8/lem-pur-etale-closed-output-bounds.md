# Stage-1 delivery: lem-pur-etale-closed-output-bounds

## Files written

- `dag/nodes/sec-six-functors/lem-pur-etale-closed-output-bounds.json`: statement, split into four steps using existing nodes. No Mathlib match for the full item.
- `citations.json`: eight entries, one for every step/node citation, copied verbatim from the cited statements.
- `searches.jsonl`: actual msearch.py records, including two LeanFinder phrasings, LeanSearch, Loogle and grep. The original creator's search records in the item are retained.
- `report.md`: this report. `prepare.py` is a sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: the item is not the unit's key node.

## Attachments

None for this item. I searched `lean/WeilConjectures/` for its exact blueprint tag and for closed-support, constructibility, amplitude and Tor terminology. `AlgebraicGeometry.Etale.exists_isLE_rightDerivedFunctor_closedUpperShriek` in `SixFunctors/Etale/Derived/ClosedUpperShriekCoproducts.lean` gives an existential upper bound, without the full constructible/Tor statement. `AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion` in `SixFunctors/Etale/Derived/Stability/UpperShriek.lean` uses a dimension bound `2d+1` and a combined cohomology/Tor input, rather than the stipulated complement bound c and the independent implication (a). The corresponding `_of_lowerStar` theorem in `Stability/ClosedImmersion.lean` assumes an already bounded direct-image object and a projection formula. None states every clause under just this item's hypotheses. The pro-etale closed-upper-shriek theorems concern another object, not the specified comparison pullback. These are not attachments.

## WANTED

None. All sources used are locally present.

## Audit of the imported item

The item was statement-only, with no proof or dependencies. Its statement is mathematically consistent with the current blueprint's closed-support calculation, and is unchanged. Its existing statement dependencies and blueprint provenance are retained. In particular, no right adjoint on the unrestricted pro-etale derived category is asserted: the pro-etale output remains exactly the ordinary constant-coefficient comparison pullback of the etale output.

The nearest blueprint ancestor is `thm-pur-general-admissibility`, proof Step 2. I read its current main-20261015 proof, the chapter record, the assigned unit, and SETUP.md's three levels. The split implements the two closed-support computations that the ancestor explicitly requests, then their comparison pullbacks. It does not change the affine-chart or smooth-projection route. The off-unit inputs are declared individually in `split_report.tool_uses` as generic closed-support or coefficient-site comparison tools. No top-level maintainer-owned tool approval was written.

The blueprint searches `ancestor`, `search 'closed amplitude'`, `search 'comparison Tor'`, `search 'closed-support'`, `search 'comparison'`, and searches for closed, constructible and Tor-amplitude terminology identified the existing amplitude, Tor and comparison nodes. None states the whole combined item; `blueprint.same_as` stays empty. The existing nodes suffice; extracting another clause as a new node would add no mathematics.

## Not duplicates

No new nodes, so there are no new/existing same-tag pairs. In particular I reused `lem-exc-closed-amplitude`, `prop-exc-closed-tor`, `lem-sf-proetale-constructible-origin`, `lem-sf-comparison-pullback-exact` and `lem-exc-comparison-tor-interval` instead of introducing specialized copies.

## Review by N8

I read delivery-errors.md sections B through E in full, including the merged copy. The following is my mathematical review of the actual split.

For the item and Steps 1 and 3 I read the main-20261015 `thm-pur-general-admissibility.proof.md`, Step 2, and the complete statement and proof files of `lem-exc-closed-amplitude` and `prop-exc-closed-tor` under `sec-six-functors-basics/sk-prop-a1-kummer/`. I opened the current DAG statements of both cited results. Step 1 uses the amplitude inclusion and its extra constructibility clause, both explicitly in `lem-exc-closed-amplitude`. Set a=r and b=s; finiteness of A, c nonnegative, the closed immersion and complementary open, vanishing on all module sheaves above c, and constructibility preservation are all in the item. The input's cohomology interval is assumed only in (a). Thus the step proves its etale assertion without finite Tor. Step 3 instead uses precisely the conclusion of `prop-exc-closed-tor`. The quotient coefficient ring, n positive, quasi-compact complement, both direct-image hypotheses and bounded constructible input match literally. Its etale Tor hypothesis is the premise of (b). Step 3 does not use Step 1's cohomological premise.

For Step 2 I read Stacks `proetale.tex`, Tag 09AL (`lemma-compare-constructible-derived`), and the constructible-origin proof under `sec-proetale-coefficients/sk-prop-sf-comparison/`. The coefficient ring A is finite, hence Noetherian, as required by Tag 09AL; the current origin node already specializes to these positive-level coefficient quotients. Its statement clause (ii) explicitly gives the equivalence with the intrinsic bounded constructible category, not just an etale-origin predicate. I read the full statement of `lem-sf-comparison-pullback-exact`, especially clause (3), and Stacks `sites-modules.tex` Tag 04JC (`lemma-flat-pullback-exact`), including why constant-ring comparison is flat. Clause (3) gives the displayed cohomology isomorphism; exactness sends zero to zero in every degree outside the interval. The cited `def-weil-constructible-intervals` explicitly defines membership as bounded constructibility plus these vanishing conditions. Thus the step uses no hidden constructibility theorem or restriction to finite-Tor inputs.

For Step 4 I read the main-20261015 statement and proof of `lem-exc-comparison-tor-interval`, its current DAG statement, and the adjacent comparison-Tor proof `lem-sf-comparison-tor-amplitude.proof.md`. The former explicitly uses ordinary derived categories, the full small pro-etale site and every module test sheaf. Its only extra input condition is bounded below; Step 3 gives bounded constructibility, hence bounded below, before the lemma is applied. The interval endpoints are ordered since r<=s and c>=0. Its forward implication preserves that exact interval. Intrinsic bounded constructibility follows separately from the same constructible-origin statement as in Step 2, now using Step 3 rather than assuming (a). I read `def-weil-proetale-tor-amplitude`: its universal quantifier is over every degree-zero module sheaf. Unfolding that definition gives exactly the final vanishing formula, including sheaves with no etale origin. No claim about commuting exceptional inverse image with arbitrary tensor factors is needed here.

The proof's non-elementary facts are all cited statements (C1), and citations.json quotes the actual clauses used (C4). None of the steps takes an object or comparison from another node's proof. The eight citations cover all uses; their union is proof_deps. The longest step is 758 characters, so none hides a >2000-character inline lemma. There is no new unsplit-node proof or disguised new node restating a clause (B1, D1-D2); all four steps specialize existing independent results. The only elementary operations inside them are substituting endpoints, preservation of zero by an exact functor, bounded implies bounded below, and unfolding the Tor predicate.

I tested small cases: K_e=0 and Z empty give zero outputs; i the identity and the empty complement give i_e^!K_e=K_e, for which the claimed enlarged interval is valid. For c=0 and r=s the conservative upper endpoint is s+1; nothing wrongly requires equality of bounds. Negative r or s causes no restriction, since all bounds are integer cohomological intervals. The residue-field level n=1 and nonreduced coefficient quotients n>1 are both covered by the stated closed-Tor result. At n>1, bounded constructibility alone need not imply finite Tor, which is why (a) and (b) are proved independently. Nonregular and nonreduced Z or T require no regularity or absolute-purity assumption. There is no codimension bound, no smoothness assumption, no identification of etale and pro-etale categories without the cited comparison, and no use of SGA sources.

I read the actual logged Mathlib search hits. LeanSearch returned scheme closed-immersion constructors and properties; LeanFinder returned generic t-structure support results on one phrasing, and ring-etaleness/cotangent results and generic homotopy/cohomology results on the other. Loogle and the Tor/upper-shriek grep returned no hits. These do not give constructible exceptional pullback or the combined specified c+1 bounds, so no Mathlib leaf was claimed. The queries recorded for this worker are exactly the executed queries; inherited creator records remain unchanged.

No statement dispute or mathematical correction was necessary. The repair is to supply the missing proof and dependency lists, retaining every hypothesis and both independent implications.

## Unfinished work

None within this one-level split. Existing cited nodes retain responsibility for their own proofs; no Lean source was written or compiler invoked. The independent maintainer review remains the project's next step.
