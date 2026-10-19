# Worker report: Q79 / lem-coef-dg-bifunctor-cofibrancy-fibrancy

## Files written

- `dag/nodes/sec-six-functors/lem-coef-dg-bifunctor-cofibrancy-fibrancy.json`: stage-1 split with four proof steps; no statement change.
- `citations.json`: five exact step/node quotations.
- `report.md`: this report and the Q79 review.

There are zero new nodes and zero new Mathlib leaves. The proof reuses the existing Mathlib leaf `lem-coef-parametrized-adjunction-corner-lifting` and the existing model/enrichment node `lem-coef-dg-model-mapping-comparison`.

## Attachments

None. I searched both read-only source checkouts for the item id, its title and the dg-bifunctor/Quillen terminology. No declaration under `WeilConjectures/` states this item without `sorry`; the upstream master files are reference material only.

## WANTED:

WANTED: no additional source. The blueprint explicitly describes this as an agent-formulated enhanced Quillen-calculus foundation; the proof uses the recorded Mathlib corner-lifting theorem and the model-structure node.

## What was wrong and what changed

The interrupted attempt left only handoff marker files and no node, report or completed delivery result. I copied the current repository item into the sandbox and rebuilt its proof from the current DAG. The imported statement is well-typed and faithful to the blueprint paragraph; no hypotheses or conclusions were changed. The prior imported Mathlib-search records were refreshed with the four searches recorded in `searches.jsonl`.

No new auxiliary node was created: the only non-elementary input needed is already stated by `lem-coef-parametrized-adjunction-corner-lifting`, whose parametrized-adjunction lifting equivalence applies after swapping the two variables. The item does not cite SGA or alter any coefficient category.

## What could not be finished

Nothing remains unfinished in the stage-1 split. No Lean source was written and no compiler or build tool was run, as required.

## Review by Q79

I read `AGENTS.md`, `coord/brief-stage1.md`, `roles/worker.md`, the stage-1 DAG document, the relevant SETUP requirements, `GOAL.md`, `coord/dag-sync.md`, and delivery-errors B-E. I read the fixed chapter record `sec-six-functors.json`, the unit record `sk-prop-sf-biduality-general.json`, the complete item node, and the ancestor blueprint proof `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/prop-coef-integral-exceptional-adjoint.md`. The item realizes that proof's paragraph-2 multivariable Quillen-calculus foundation and leaves the target statement unchanged.

I read the complete statements of `lem-coef-dg-model-mapping-comparison` and `lem-coef-parametrized-adjunction-corner-lifting`. The first explicitly says that an object is cofibrant when its initial map is a cofibration and that the model classes form the required lifting systems. The second states verbatim the equivalence
`(i □_H j) ⟂ p ↔ j ⟂ ⟨i,p⟩_R` for a parametrized adjunction with the relevant pushout and pullback corners. Those are exactly the facts quoted in `citations.json`.

Step 1 checks all initial-object hypotheses: each partial of the two-variable left adjoint preserves an initial object, so the pushout product of the two initial cofibrations is the initial map into `B(P,Q)`. The cited model node supplies the cofibrancy interpretation. I checked the edge cases `P=0`, `Q=0`, and both initial, where the displayed pushout product reduces to an identity/initial map as expected.

Step 2 fixes a cofibrant `Q` and substitutes `0 -> Q` for the second cofibration. The three zero-input values of `B` are initial, so the pushout product is exactly `B(i,Q)`. The stated hypothesis gives the cofibration and trivial-cofibration conclusions; swapping variables gives the `B(P,-)` clause. This is a direct one-line specialization, marked elementary, and uses no unstated stability assumption.

Step 3 applies the cited corner theorem with `H(c,d)=B(d,c)` and `R(c,e)=A(c,e)`, first arrow `0_N -> Q`, and second arrow an arbitrary map `u` in `M`. The right adjunction identifies maps into `A(0_N,I)` with maps out of the initial object `B(P,0_N)`, so `A(0_N,I)` is terminal. The pullback corner therefore reduces to `A(Q,p)`. For a trivial cofibration `u`, Step 2 makes the pushout product trivial, so it lifts against every fibration; the corner equivalence gives the right lifting property of `A(Q,p)` against every trivial cofibration. For a trivial fibration `p`, the same argument with arbitrary cofibrations `u` gives the trivial-fibration class. The weak-factorization-system clause of `lem-coef-dg-model-mapping-comparison`, explicitly cited in Steps 3 and 4, identifies these right lifting classes with fibrations and trivial fibrations. The terminal map `I -> *` and preservation of terminal objects by a right adjoint then give fibrancy of `A(Q,I)`. I verified that the swapped parametrized-adjunction variables have the correct source and target categories and that the corner map specializes to `A(Q,p)`.

Step 4 repeats the same check with `H(c,d)=B(c,d)` and `R(c,e)=A'(c,e)`, so the corner theorem yields fibrations and trivial fibrations for `A'(P,-)` and hence fibrancy on fibrant inputs. I checked the variance of the second enriched adjunction and the terminal-object argument separately.

I searched the whole DAG and blueprint for the corner-lifting statement and for the item's title and key phrases. The existing corner-lifting node is a Mathlib leaf and is more general than the use here; no duplicate or clause-restatement node is introduced. The dependency closure of the two cited nodes does not return to this item. All four Mathlib searches were run through `msearch.py` and are recorded in `searches.jsonl`; the search results found only general model-category infrastructure plus the existing parametrized-adjunction theorem, so the item itself remains a non-Mathlib statement. Small cases and the absence of a stability hypothesis were checked explicitly. No SGA source is cited, and no tool-use exception is needed.

## Not duplicates

- `lem-coef-dg-bifunctor-cofibrancy-fibrancy` vs `lem-coef-parametrized-adjunction-corner-lifting`: the existing node is a general categorical lifting equivalence for arbitrary parametrized adjunctions; this item adds model-category hypotheses and derives cofibrancy, separate Quillen restrictions, and right-adjoint fibrancy.
- `lem-coef-dg-bifunctor-cofibrancy-fibrancy` vs `lem-coef-dg-model-mapping-comparison`: the existing node compares enriched model categories and defines cofibrant/fibrant objects; this item is the pushout-product theorem that uses those notions.

## Delivery resumption correction

On resumption I checked the saved corner specialization against the full statement of `lem-coef-parametrized-adjunction-corner-lifting`. Its first arrow must be the initial map `0_N -> Q`, not the identity of Q: the latter would give an identity pushout product and cannot prove the claim. I corrected Step 3, proved directly by the adjunction that `A(0_N,I)` is terminal, and wrote out the pullback corner that reduces to `A(Q,p)`. The symmetric argument of Step 4 uses `0_M -> P`. I also made both steps explicitly cite the model weak-factorization-system statement, adding its verbatim quote to the citation ledger. No statement, search query, or new-node inventory changed. All proof steps remain shorter than 2000 characters.
