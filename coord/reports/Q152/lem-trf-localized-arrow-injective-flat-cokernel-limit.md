# Stage-1 report: lem-trf-localized-arrow-injective-flat-cokernel-limit

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-localized-arrow-injective-flat-cokernel-limit.json`: statement, split, not a Mathlib leaf. Statement and statement dependencies preserved; three complete proof steps added. Recorded the actual Q152 Mathlib searches while retaining the imported searches.
- `citations.json`: one entry for each node used in each numbered step, with verbatim statement quotes.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean written or compiled. No unit realization changes: this is not the unit's key node.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and for localized cokernels/flat cokernels. Existing residue-kernel results and the flat-mod-injective theorem concern different hypotheses and do not give this whole varying-ring directed-system statement. Read the existing localized-base-change quotient-flatness theorem as a reusable ingredient, not an attachment of the item.

## WANTED

None. All mathematical sources used are in `literature/stacks-project/algebra.tex`.

## Findings and changes

The input was genuinely unsplit, and the sandbox had no earlier item, report, or search log. There was no released repair note for this id. The statement is correct and needs no correction. In particular it explicitly assumes element representatives and eventual detection of equality for the additive colimits; these make the injectivity argument elementary. It also assumes the strong scalar-extension isomorphisms at every stage, which suffice for the cokernel comparison at every stage, including stages before the eventual injectivity/flatness tail.

The source's last sentence in Tag 046Y omits the limit argument. The split writes it out using the assumed eventual-zero property (the content of 00D7), tensor right exactness (00DF), and the zero-ideal specialization of the existing localized-base-change quotient-flatness node (00MO's first proof paragraph). No Noetherian local criterion is applied to the present arbitrary rings.

I read `dag/chapters/sec-trace-formula.json`, `dag/units/sk-i-curve-zero.json`, and the main-20261015 blueprint file for `lem-trf-local-term-locality`. This item is a generic algebraic tool far down the valuation-ring branch, not the key unit statement. Its split stays within the inherited algebraic route and does not invoke SGA.

## Searches and existing-node reuse

Searched the whole DAG by the item id, Stacks tags 00DF, 00D7, 00MO and 00HT, and by flat localization, tensor right exactness and localized base change. Read the actual statements of the reused nodes. Ran `tools/blueprint_refs.py ancestor` and whole-blueprint searches for `flat cokernel`, `tensor product exact`, `localized`, and `cokernel`; no imported blueprint node states the item. The nearest blueprint ancestor is `lem-trf-local-term-locality`. Its inherited `blueprint.from.place` already gives the exact 046Y final-passage role and remains filled; `same_as` is empty.

Ran msearch.py with the item id and group Q152: LeanFinder twice with distinct formulations, Loogle `Module.Flat, TensorProduct`, grep for colimit/injectivity and flat/cokernel combinations, and LeanSearch for the entire varying-ring statement. All calls succeeded; exact queries and returned top hits are in `searches.jsonl` and the appended `mathlib_searches`. The hits give ingredients, not this complete conjunction. Read `Module.DirectLimit.lift_injective` and its surrounding source: it concerns a compatible family of maps to one target over a fixed scalar ring; it does not give the localized varying-ring flat-cokernel theorem. Read `lTensor_exact` and `rTensor_exact` in Mathlib's `LinearAlgebra/TensorProduct/RightExactness.lean` to confirm the existing right-exactness leaf used in step 2. No candidate warranted making the whole item a Mathlib leaf.

## Not duplicates

No new nodes were created. Existing `lem-weil-pbc-tensor-right-exact` supplies the cokernel argument; existing `lem-weil-pbc-localized-base-change-quotient-flat` supplies flatness with ideal zero. Existing localization/base-change tensor lemmas were therefore not recreated. The elementary eventual-kernel argument and isomorphism transport are proof steps, not additional nodes.

## Review by Q152

I checked the split against delivery-errors B through E with the cited statements and Stacks source open. The item source was Tag 046Y, `lemma-mod-injective-general`, especially its final sentence after the Noetherian-stage result; I also read Tag 00D7, `lemma-zero-directed-limit`, Tag 00DF, `lemma-tensor-product-exact`, and Tag 00MO, `lemma-another-variant-local-criterion-flatness`, first proof paragraph. There are no new node sources to review.

Step 1 uses no cited theorem: the statement itself assumes that every element has a representative and that equality is eventually detected. For a representative of a kernel element I explicitly passed its zero image to a later stage and then to a common upper bound with i_0. The two commuting-map identities and injectivity at that last stage force the representative to vanish. This proves kernel zero and hence injectivity by taking differences. Directedness is used only for that common upper bound. No transition map is assumed injective and no scalar-extension map is assumed left exact.

Step 2 cites `lem-weil-pbc-tensor-right-exact`, whose statement explicitly includes exactness after tensoring and surjectivity of the last map. Applying it to the quotient sequence gives precisely the kernel and surjectivity asserted in this step. The two given scalar-extension isomorphisms carry the preceding arrow to u, so the kernel is u(M). I wrote the inverse of the induced quotient map and checked its well-definedness and both compositions using the surjective quotient maps. Checking a pure tensor gives exactly [y] tensor s mapped to s[nu_i(y)]. This argument works for every index, and makes no injectivity assumption at early indices. This is an application of the cited theorem plus an elementary quotient argument, not a new lemma or an unsupported identification.

Step 3 cites `lem-weil-pbc-localized-base-change-quotient-flat`. I read its complete statement and its upstream declaration `Module.flat_quotient_localized_baseChange` in `WeilConjectures/RingTheory/LocalizedBaseChangeQuotientFlat.lean`. Its statement explicitly excludes locality, Noetherianity, finiteness and properness requirements. Substituting its four rings by (R_i0,S_i0,R,S), its module by C_i0 and its ideal by zero gives exactly the flatness needed. The ring cocones give both commuting scalar towers and the assumed pure-tensor formula gives its localization witness. Its input flatness is precisely the tail assumption at i_0; its output, after quotient by zero and the unit tensor identification, is R-flatness of S tensor over S_i0 with C_i0. I wrote the maps for those identifications, tensor symmetry, and the reason flatness transports through the step-2 R-linear isomorphism. The cited tensor-product definition supplies universal bilinear maps, pure-tensor generation and tensor functoriality; the flat-module definition supplies the injectivity test used for this last transport. Every quote in citations.json is literally in the cited statement; no proof or definition is substituted for a stronger theorem.

The only off-unit non-leaf theorem used is the generic localized-base-change quotient-flatness tool from sk-thm-p1, declared in split_report.tool_uses for maintainer review. It is an algebraic tool and does not change the curve-unit route. I checked that its dependency closure and that of tensor right exactness do not reach this item, so the split introduces no cycle through these citations.

Small-case checks: for a one-element directed set step 1 is ordinary injectivity and step 2 is right exactness of scalar extension; zero modules give zero cokernels; the identity and zero maps behave as their injectivity hypotheses require; transition maps can kill elements, which is why step 1 passes to the later stage; arbitrary early noninjective arrows do not affect the quotient comparison; the zero-ring/localization-killing-everything case gives zero target modules and a flat zero cokernel. The zero ideal is allowed in the actual localized-base-change theorem, including when the base ring is zero. No nonzero module or ring assumption is introduced.

B: no new nodes, no unintroduced notions, no fabricated Mathlib searches. C: every non-elementary theorem is explicitly cited, every citation was checked by its statement, and the generic tool use is declared. D: the proof contains the actual kernel and quotient arguments, rather than moving a clause to a new node. E: all scalar towers, tail indices and localization hypotheses were matched; the canonical maps and their inverses were written instead of an unexplained transport. All proof steps are under 2000 characters. No source error or disputed statement was found, and no statement was weakened.

## Unfinished work

None in stage 1. This is a natural-language split only; the requested server checks and delivery are recorded by the delivery tool.
