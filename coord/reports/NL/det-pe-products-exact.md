# Stage-1 worker report: det-pe-products-exact

## Files written

- `dag/nodes/sec-proetale-coefficients/det-pe-products-exact.json`: kept the imported statement and split its proof into two steps; status is now `split`.
- `citations.json`: three verbatim statement quotations for the three node uses in the two steps.
- No new nodes and no Mathlib leaves.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for `det-pe-products-exact`, the notion of exact products of pro-étale module sheaves, and the docstring tag `(blueprint: det-pe-products-exact)`. There is no declaration stating this item without `sorry`.

## WANTED

None.

## What was wrong in the imported split

The imported proof was mathematically on the right route but compressed products, module exactness, and endpoint exactness into one paragraph. I made the two uses of the existing conservativity statement explicit: its middle-term criterion is applied to the full sequence, and the same criterion with a zero endpoint gives injectivity and surjectivity. The statement itself is unchanged. No clause was moved into a new node because the module product argument is a coordinatewise calculation with choice. The whole-blueprint search for `det-pe-products-exact` found only the item itself; no duplicate node exists.

## Not duplicates

No new nodes were created, so there are no new-versus-existing node pairs to distinguish. The whole DAG and blueprint searches found only the three existing dependencies used below.

## Unfinished work

None. No Lean file was written and no compiler, Lake, or build command was run.

## Review by NL

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, and delivery-errors sections B–E. The item source is `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-pe-products/det-pe-products-exact.md` with its proof in the adjacent `.proof.md`; the source has exactly one paragraph and the imported item statement agrees with it. The chapter and proposition section records in the same blueprint directory were also read. The exact-tag and keyword search of the read-only slopmaster2 source found no completed declaration, so this is a split rather than an attachment.

Step 1 uses the statement of `det-pe-sections-limits-colimits`, which explicitly says that evaluation on an affine weakly contractible object preserves all limits, hence products. It also uses `det-pe-wc-sections-exact`, whose statement says that evaluation on a weakly contractible affine is an exact functor to `R(W)`-modules. I checked that the object called `W` in the step is the `U` of that exactness statement. The remaining assertion is written out: products of module maps are coordinatewise; kernels and injectivity are coordinatewise, while a tuple in the target is lifted by choosing one preimage in each factor (the allowed axiom of choice). This does not require finite products, projectivity, or any unmentioned hypothesis.

Step 2 uses clause 1 of `det-pe-sections-conservative`. That clause states exactly that exactness at the middle of a sequence of module sheaves is equivalent to exactness after evaluation on every affine weakly contractible object. Since Step 1 establishes the evaluated short exact sequence, it gives middle exactness. I explicitly apply the same clause to `0 → ∏ A_i → ∏ B_i` and to `∏ B_i → ∏ C_i → 0`; the evaluated sequences are exact because the zero terms are zero, so the first map is monic and the second epic. Together these are the required short exact sequence. This avoids claiming that the cited conservativity statement itself says endpoint exactness without explaining the zero-term applications.

I checked each quotation in `citations.json` character-for-character against the current statement field of its cited node. The proof dependencies are exactly the union of the two steps' uses. I searched the full DAG and blueprint for the item's key words and found no duplicate statement. The item blueprint metadata now records `same_as: []`, while its imported `blueprint.is` and `blueprint.from` fields remain intact; the split report records which sentences of the source paragraph each step realizes. Small cases (empty index set, singleton index set, and zero modules) satisfy the coordinatewise argument, and no extra assumptions on the index set or on the ring are used.

## Dry run

I ran `python3 /home/ubuntu/weil-launcher-nt/deliver.py NL det-pe-products-exact --no-push` from this sandbox; it passed and this worker did not push or deliver.

Final dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver.py NL det-pe-products-exact --no-push` printed `OK (not pushed) deliver/NL/det-pe-products-exact at bc5f1a2d3e: preflight passed`. No delivery was pushed; the accepted sandbox is left for the second reader.

## Second reading by NL

- Item statement: checked against `det-pe-products-exact.md` in the main-20261015 blueprint, hypothesis by hypothesis; verdict: agrees, including arbitrary sets, zero and singleton index cases, and the equivalent exact-functor clause.
- Step 1: checked against the statements of `det-pe-sections-limits-colimits` and `det-pe-wc-sections-exact`; verdict: both citations supply the asserted evaluation and exactness, and the remaining product-of-modules argument is an explicit coordinatewise calculation with choice.
- Step 2: checked against clause 1 of `det-pe-sections-conservative`; verdict: the evaluated sequence gives middle exactness, while the two zero-endpoint applications give injectivity and surjectivity, so no endpoint claim is taken from an unstated clause.
- New nodes: none; B1–B7 and duplicate-node checks are vacuous, and no Mathlib leaf is introduced.
- Dependency statements: opened all three cited node files in the shared DAG and verified that each says exactly the fact used by its step; no proof-only facts are imported.
- Edge cases: checked empty and singleton products and zero modules; the coordinatewise argument and the zero-endpoint applications remain valid.
- Changes made: replaced the citations entry for `det-pe-sections-conservative` with a verbatim quotation of its clause 1 (the worker's quotation was only the introductory definition of `\\mathcal W` and did not state the criterion used); no mathematical statement or proof step changed.
