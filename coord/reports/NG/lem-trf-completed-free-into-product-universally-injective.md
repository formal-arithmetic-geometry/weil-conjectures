# Stage-1 report: lem-trf-completed-free-into-product-universally-injective

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-completed-free-into-product-universally-injective.json` — statement; split proof of Tag 05BC.
- `citations.json` — verbatim statement quotes for every non-elementary item step.

## Attachments

No finished declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states this item. No attachment was found.

## WANTED

None. The proof source is present in `literature/stacks-project/more-algebra.tex` and `algebra.tex`.

## Not duplicates

No existing DAG node states Tag 05BC's completed-direct-sum-to-product injectivity, its convergent-family lifting lemma, or the universally-exact finite-presentation criterion.

## What was checked and changed

The imported item statement agrees with More on Algebra, Tag 05BC: $R$ is Noetherian and $I$-adically complete, the completion is the inverse limit of the direct sums of $R/I^n$, and universal injectivity means injectivity after tensoring with every $R$-module. I retained the three imported definition dependencies and did not add hypotheses. I searched the source tree for a finished declaration by the item id and by the notions “completed free”, “direct sum”, “product”, and “universally injective”; no project declaration without `sorry` matched.

I read the complete Tag 05BC proof at `literature/stacks-project/more-algebra.tex` lines 6322–6392 and the criterion at `literature/stacks-project/algebra.tex`, Tag 058K. The first new node records the coordinate description of a completion element and the resulting ordinary injectivity. Its finiteness condition is exactly that each reduction modulo $I^n$ has finite support, and completeness of $R$ supplies unique coordinate limits.

The second new node isolates the Artin–Rees lifting used in the finite-module tensor argument. I checked its hypotheses against the existing `lem-weil-pbc-artin-rees`: the relation module is the image of a map between finite free modules, hence a submodule of the finite module $R^{\oplus m}$, and the Artin–Rees bound gives a uniform loss of $c$ powers of $I$. The proof step explains that choosing preimages with this shifted order preserves the finite-support condition at every level.

The third new node states the Tag 058K equivalence between universal injectivity and injectivity after tensoring with every finitely presented module; over Noetherian rings the finite and finitely presented tests agree. I checked that the item’s coordinate map is injective before applying this criterion. In the item proof, Step 1 cites the coordinate node, Step 3 cites exactly the Artin–Rees lifting statement, and Step 4 cites exactly the finite-presentation criterion; the finite presentation and tensor-kernel setup in Step 2 is elementary.

I ran the required Mathlib searches for the item and recorded them in the item search log. Mathlib has `AdicCompletion.map_injective` and `Ideal.exists_pow_inf_eq_pow_smul`, but neither states the needed infinite product target; the universal-injectivity criterion is already represented by the existing DAG node `lem-trf-universal-injective-finite-test`. The server-side `check_dag` and `review_split` checks both passed.

## Review by NG

I read the item source and every source named by the three new nodes. I verified the coordinate description directly against Tag 05BC. The existing Artin–Rees node gives the needed intersection bound for the finite relation module, and the existing `lem-trf-universal-injective-finite-test` node states the exact tensor test used in Step 4, including the Noetherian finite/finitely-presented identification.

I checked the hypotheses in the Tag 05BC argument: completeness is used only to obtain coordinate limits, Noetherianity is used for Artin–Rees and the finite-presentation criterion, and the finite presentation of $Q$ is used to obtain the relation map. I corrected the new-node metadata after the first server check by adding the fixed chapter and unit fields; the subsequent `check_dag` and `review_split` runs passed. `citations.json` contains verbatim quotes for all non-elementary uses, and the item’s `proof_deps` is the union of the cited nodes.

## What remains

No new supporting nodes were needed: the two non-elementary ingredients are existing DAG nodes. No Lean files were written and no compiler or build tool was run. No Lean files were written and no compiler or build tool was run.
