# Stage-1 delivery: lem-trf-finitely-presented-over-subring

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finitely-presented-over-subring.json`: item, status split, with a complete five-step proof following Stacks Tag 0561.
- `dag/nodes/sec-trace-formula/lem-trf-polynomial-action-reduction.json`: new statement-only auxiliary node, unsplit and with no Mathlib match.
- `citations.json`: verbatim quotations for every cited node in the item's proof.
- `searches.jsonl`: actual Mathlib search records for the item and auxiliary node.
- `report.md`: this report.

There is one new node and zero Mathlib leaves.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact item id, the blueprint tag, and finite-presentation transfer terminology. No sorry-free project declaration states this item. The existing Mathlib declarations concern finite presentation of an algebra or transitivity for modules and do not state the module-over-finite-type-subring result.

## WANTED

None. The cited Stacks source is present locally at `literature/stacks-project/algebra.tex`.

## Not duplicates

- `lem-trf-polynomial-action-reduction` vs `lem-trf-finitely-presented-over-subring`: the auxiliary node proves only reduction of polynomial coefficients under generator-action relations; the item additionally assumes finite presentation over R and concludes finite presentation over S.

## What was wrong and what changed

The imported item had an empty proof. I retained its statement and dependencies and wrote the Tag 0561 construction. The degree-lowering argument in the source is a genuine auxiliary claim, so I made it the smaller statement-only node `lem-trf-polynomial-action-reduction` rather than hiding it in an elementary step. The source's phrase “relations generate the kernel” is used exactly as finite presentation: finite R-generators and finitely many relation vectors. The final injectivity step uses the original R-relation vectors, so no relation from the quotient ideal J is silently assumed.

The item and auxiliary node are supporting algebra in the inherited valuation/flat-module branch below the normal-cone locality ancestry. Their blueprint places now describe that supporting role explicitly. The unit `sk-i-curve-zero` remains unchanged: this split does not claim that Tag 0561 is its local-term vanishing argument, and it does not replace any step of that unit. The existing reviewed valuation descendants consume this item as their finite-presentation transfer input.

## Review by Q93

I read the complete item statement and proof of Stacks Algebra Lemma 0561 at `literature/stacks-project/algebra.tex`, lines 584–628, and compared each hypothesis with the item: an arbitrary ring map R to S, finite type of S over R, and finite presentation of the S-module M after restricting scalars to R. I also read the exact statements of `def-weil-pbc-finite-type-algebra` and `def-sc-finitely-presented-module`; the former supplies a polynomial surjection and the latter supplies finite generators and finitely many relation vectors.

Step 1 uses exactly those two definitions to choose polynomial generators of S and generators/relations for M over R. Step 2 constructs N with the original relation vectors and the finitely many action relations, so its displayed finite presentation is over S. Step 3 checks that the assignment to M respects every relation and gives a surjective S-linear map. Step 4 uses the auxiliary node's stated polynomial-action reduction and the finite-presentation relation vectors to prove injectivity; I checked that the auxiliary statement says precisely that every element reduces to an R-linear combination of the generators. Step 5 then transfers the finite presentation across the resulting isomorphism.

I checked the small cases M=0, S=R, zero polynomial-generator list, and one generator: the construction and reduction remain valid. I reread the inherited chapter and unit records and the current blueprint ancestry. The item is not the unit key statement; it is a generic algebra input consumed by the reviewed valuation descendants. The revised blueprint place and report make that supporting role explicit, while the unit's local-term statement and route remain untouched. No SGA source is used.

## Second reading by Q93

I reread the item, auxiliary node, citations, and the current valuation descendants that consume the item. The Tag 0561 hypotheses and conclusion are unchanged; the auxiliary statement is strictly smaller and does not restate the item. Every citation quote is a verbatim substring of the cited statement, proof_deps is the union of uses, and the degree-reduction calculation remains isolated. I also reread the chapter/unit records and confirmed the revised blueprint wording identifies this as supporting algebra without changing the unit statement or route. Empty and zero-module cases remain valid. No further changes were needed.
