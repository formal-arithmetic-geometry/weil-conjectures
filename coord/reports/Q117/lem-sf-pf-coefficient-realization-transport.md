# Q117: lem-sf-pf-coefficient-realization-transport — repair of ba889bdb80

## Files written

- `dag/nodes/sec-six-functors/lem-sf-pf-coefficient-realization-transport.json`: five elementary substitution steps; the statement now explicitly binds every formula used. No exact Mathlib match.
- `citations.json`: empty because the revised proof uses only its own hypotheses and the locally displayed definitions; there are no proof-node citations.
- `report.md`: revised source and mathematical review, retaining the search findings and scope of the earlier attempt.

No new nodes and no Mathlib leaves. The original ancestry, source, title, unit, created record, and logged searches are retained. The definition remains a statement dependency for the operation types; it is no longer cited as a proof of formulas that a typed-only version does not state. No other node or unit is modified.

## Attachments

None. The exact blueprint tag and coefficient/realization name searches in `WeilConjectures/` yield no declaration stating the complete assertion. The earlier source searches remain relevant: `WeilConjectures/SixFunctors/Etale/Derived/Package.lean`, lines 51–57, explicitly excludes the finite-reduction, scalar-extension and pro-etale-realization comparison clauses. I reread this passage. The earlier inspected `WeilConjectures/CategoryTheory/Adjunction/ProjectionMapCompat.lean` gives particular projection-map identities, not the four-map transport assertion with supplied comparison/refinement cocycles.

## WANTED

None. This is an agent-written proof of a conditional formal assertion, not a claim that geometric coefficient or realization comparison data exist.

## Statement corrected

STATEMENT-DISPUTED (formula reference, not truth of the conditional transport assertion): the returned version names pi_p, e_p, beta and gamma by a reference to `def-exchange-projection`. The return reports a cited statement containing only the typed Ex_*, Ex_! and PF. Such a statement does not bind pi_p or the factorization of PF through gamma, so the reference alone does not specify the terms used. This is a definition/type-specification failure: from the three typed transformations alone one cannot even form the cited expression `Rp_*(gamma) pi_p`. No counterexample to the conditional algebraic transport assertion is claimed.

The current shared copy of `def-exchange-projection` does display all these formulas, whereas `sk-def-sf-exchanges` does not display pi, beta or gamma. The first dry run of the retained sandbox passed; an attempted delivery then reported that it was exactly the returned head ba889bdb80 and pushed nothing. Therefore merely revalidating those retained citations was not a repair.

The actual repair replaces the ambiguous formula reference in this item's statement by explicit local definitions of a, pi, e, PF and Ex!, with the types of the supplied mu, theta, beta and gamma. These are the unit/tensor/counit, unit/square/counit, and compactification composites already meant by the former statement. No hypothesis or conclusion has been added or removed: preserving beta/gamma, tensor and square comparisons was already a hypothesis; their existence remains supplied data. In particular the assertion remains conditional for closed coefficient domains, forward transport needs no faithfulness, and refinement compatibility remains conditional on primitive intertwining. The correction neither changes a target nor asserts unconditional higher-coefficient operation existence or compactification independence.

## Sources and route

I read the chapter and unit records, the three levels in SETUP.md, GOAL.md, coord/dag-sync.md, and delivery-errors B–E and the cited F review requirements. I read `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md` and `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sf-exchanges/def-exchange-projection.md`, alongside the full current statements of `def-exchange-projection` and `sk-def-sf-exchanges`.

The blueprint's proper projection map is the transpose of counit tensor identity through pullback monoidality; expanding the transpose gives R(a) eta. Its proper exchange is the square-comparison/counit mate; expanding the transpose gives the three arrows defining e. Its open compactification factors give beta and gamma with exactly the displayed source and target. The expansion uses no base-change isomorphism theorem. The final coefficient-compatibility clause motivates this helper; geometric existence/preservation remains with its parent proof's comparison theorems. I preserve this route and do not use SGA. The helper is not the unit's key node, so no unit realization record changes.

## Not duplicates

No new nodes are created. The existing recorded DAG/blueprint searches for coefficient realization, finite reduction, comparison functor and the comparison/unit/counit terminology are retained. I reran `blueprint_refs.py search 'coefficient realization'` (zero blueprint nodes), and ancestor identifies `prop-sf-pf-coherence`. Expanding the expressions inside this conditional theorem avoids creating duplicate definition nodes for formulas already present in the current shared definition. There is no new lemma that restates a clause.

## Mathlib searches and results read

All earlier query records and `searches.jsonl` are retained. The search question is unchanged by making its formulas explicit, so the recorded searches are reused rather than repeated. The semantic coefficient-realization hits are first-order logical realization lemmas or polynomial/base-change presentation facts. The Loogle hits concern monoidal units/counits and induced monoid functors, not comparison of two supplied operation systems with the four stated maps.

The previous reader inspected `CategoryTheory.Adjunction.unit_app_tensor_comp_map_δ` and `map_μ_comp_counit_app_tensor`, in `Mathlib/CategoryTheory/Monoidal/Functor.lean`, lines 1024–1039, and the monoidal unit/counit instances in `Monoidal/NaturalTransformation.lean`, lines 140–157. These are constituent laws for one adjunction, not a one-line specialization of this assertion. The second semantic phrasing returned `CategoryTheory.expComparison`, Frobenius/exponential isomorphism criteria and exponentiable-morphism composition laws; the recorded reading of `Mathlib/CategoryTheory/Monoidal/Closed/Functor.lean`, lines 49–80, concerns Cartesian closed functors. The previous valid grep used `CategoryTheory`, correcting an earlier `Mathlib/CategoryTheory` argument to a wrapper that already prepends Mathlib. Its seven hits are retained. No unavailable service is treated as absence evidence and no unexecuted query is added.

## Unfinished work

None within this one-level split. Establishing the supplied comparison data in geometric coefficient domains remains outside this conditional lemma, exactly as before.

## Review by Q117

For the return's C1/C4 point, I checked every expression actually used against its binding, not just against a node title. The revised statement itself gives a=(counit tensor 1) mu and pi=R(a) eta, the three arrows of e, the exact types of beta/gamma and the ordered definitions of PF and Ex!. Thus no step now takes these formulas or any non-elementary theorem from a typed-only definition. The removed six citation excerpts were from the fuller current shared definition, but the proof no longer relies on their availability in the review snapshot. `citations.json` is empty for this reason; there is no hidden external proof citation.

Step 1 writes the two-square pasting equation using functoriality and substitutes the two locally bound factors of a and pi. The supplied comparison for Rp_* is natural; applying it to a gives the whiskered equation. All intermediate inputs belong to the explicitly closed domains. This uses no projection-formula invertibility.

Step 2 substitutes the three locally defined arrows of e. The unit is the unit for p' at Q=Lg*Rp_*M; the counit is the one for p at M; theta is the pullback square comparison at Rp_*M. These types match in order. Naturality of the supplied pullback and direct-image comparisons and the same written pasting identity give the result. No theorem about mate transport is cited or assumed.

Step 3 simply instantiates the original hypothesis that the supplied data intertwine beta and gamma, now with both maps typed in this statement. Gamma includes the actual pullback-composition comparison Lj*Lp* to Lf*. The proof does not deduce open base change, open projection isomorphy, full faithfulness or exactness from a definition: beta and gamma were supplied isomorphisms before and remain supplied isomorphisms.

Step 4 substitutes the locally defined PF=Rp_*(gamma) pi and Ex!=Rp'_*(beta) e, evaluating e at j_!K. Whiskering is naturality of the supplied functor comparisons; tensoring an arrow with an identity is naturality of the tensor comparison in its two inputs. Repeating the two-square identity proves the assertion for every finite composable route, hence for the named routes. There is no claim that the routes coincide unless an equality is supplied for transport.

Step 5 writes the calculation for successive comparison functors: the comparison is c S(b), exactly the assumed cocycle. Inserting primitive refinement comparisons gives the refinement assertion by the same pasting calculation, only when such data are supplied. Applying a functor to u=v and cancelling the invertible endpoint comparison proves forward equality transport. No faithfulness is used.

For E7, the statement clarification is explicitly recorded above and supplies only the missing meaning of its terms, without changing coefficient categories or weakening conclusions. For F1/F2, this review distinguishes the two actual definition statements I opened and no longer claims that the typed-only version contains unprinted formulas. I checked the source's transpose descriptions against the expanded arrows, rather than certifying a reference by name. This is a substantive change from returned head ba889bdb80, not a rebase-only push.

I tested identity comparisons, zero inputs and noninvertible arrows, an empty scheme/domain where meaningful, and nonfaithful functors. Every calculation uses only functoriality, the supplied primitive equations and invertibility of endpoint comparisons. Failure of geometric comparison existence simply means the hypotheses are not supplied; no field object is reduced to a finite coefficient object. All five proof steps are below 2000 characters and consist of one routine substitution/pasting calculation each, with no concealed geometric lemma. B–E introduce no new-node, duplicate, circularity or source-route issue. No Lean was written and no compiler, Lake or build tool was run.
