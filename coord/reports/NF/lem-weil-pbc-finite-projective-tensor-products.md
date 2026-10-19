# Stage-1 report: lem-weil-pbc-finite-projective-tensor-products

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-projective-tensor-products.json`: statement, split into four proof steps; no Mathlib match.
- `citations.json`: verbatim quotations for every cited node in every step.
- `report.md`: this report.

No new nodes or Mathlib leaves were created. The item statement is unchanged; its statement dependencies now include the derived-tensor definition used by the displayed tensor notation.

## Attachments

None. I searched the supplied slopmaster2 source for the exact blueprint id and for finite-projective/product/tensor declarations. No sorry-free declaration states this derived sheaf-product comparison. The upstream master declarations are reference material only and were not treated as proofs.

## WANTED

None.

## Corrections and scope

The imported item had `status: split` but no proof steps or proof dependencies. I supplied the missing proof route rather than creating a node that merely restated the item's conclusion. The four steps implement the blueprint's final sentence: represent derived tensor by the bounded finite-projective complex, prove the finite-free/direct-summand product comparison, assemble it through the bounded total complex, and pass to the termwise derived-product model. The proof keeps all products and tensors in the completed sheaf category over `A_T`; it does not identify this with an ordinary `D(A)` or with condensed coefficients.

No existing DAG node states the full comparison. The finite direct-sum and direct-summand calculation is elementary, so it is a proof step rather than a new node. Existing nodes are used for the derived-tensor convention, total-complex construction, exact countable products, derived inverse-limit products, and their termwise representation.

## Review by NF

I read the item's master blueprint source `literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/lem-weil-pbc-finite-reduction-reconstruction.md`, the parent node `lem-weil-pbc-finite-reduction-reconstruction`, and the statements of every dependency cited by the four steps. Step 1 uses `def-weil-derived-tensor` for K-flat computation and `def-weil-pbc-adic-coefficient-datum` for the ambient category `D(Mod(A_T))`; those statements say exactly that derived tensor is represented by a K-flat tensor complex and that the coefficient category is sheaves of `A_T`-modules. Step 2 is the finite-free distributivity and idempotent/direct-summand calculation written out directly from the hypothesis that every term is a direct summand of `A_T^{N_j}`; no additional theorem is hidden in a citation.

For step 3 I opened `lem-weil-proetale-countable-products-exact`, whose statement gives existence, sectionwise computation, and exactness of countable products of module sheaves, and `def-pc-tensor-complex-sheaves`, whose statement gives the finite direct-sum total-complex terms and sign differential. These are precisely the facts used to assemble the degreewise comparisons and pass from complexes to the derived category. For step 4 I opened `def-weil-pbc-derived-inverse-limit`, which states that the derived products are termwise products in `D(T_{Proet},A)`, and `prop-weil-pbc-derived-product-representation`, which states the representative by a product of evaluations. The final naturality claim follows because each map is induced by product projections and the tensor bifunctor, as required by the displayed canonical comparison.

I checked edge cases in the argument: rank zero terms give zero on both sides; a one-term complex reduces to finite distributivity; a zero family member contributes a zero factor; and identity transitions preserve the same projection formula. No flatness of the arbitrary `C_n` is assumed: K-flat resolutions are used only to represent their derived tensors. The Mathlib searches were rerun with `msearch.py` using LeanFinder, Loogle, grep, and LeanSearch; LeanFinder returned only condensed-projectivity/Tor APIs, Loogle had no applicable preservation theorem, grep found only unrelated categorical tensor-preservation declarations, and LeanSearch was unavailable. Thus this is not a Mathlib leaf.

Against delivery-errors B--E, the statement is self-contained and retains the exact coefficient category and hypotheses; no clause was moved into a duplicate node; every non-elementary fact in the steps has a cited node whose statement was opened and checked; the direct-summand calculation is explicitly elementary; and no circular dependency is introduced. The item has no source-statement correction and no duplicate pair to report. No Lean, compiler, Lake, or build command was run.

## Unfinished work

None at this one-level split. The independent second reader is expected to perform the delivery dry run.

Dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver.py NF lem-weil-pbc-finite-projective-tensor-products --no-push` printed `OK (not pushed)` at commit `7e7a481a62`; preflight passed. The off-unit exact-product theorem is recorded in `split_report.tool_uses` as required.

## Second reading by NF

- Item statement: checked against the parent blueprint sentence and the completed-coefficient category definition; the bounded finite-projective hypothesis, arbitrary countable family, canonical comparison, and functoriality are all retained.
- Step 1: checked against `def-weil-derived-tensor`, `def-weil-pbc-adic-coefficient-datum`, and `def-weil-pbc-derived-inverse-limit`; repaired the invalid bounded-K-flat assumption by using K-injective representatives and explicitly stating why a bounded finite-projective complex is K-flat.
- Step 2: checked the finite-free calculation and retract argument on rank zero, rank one, and an idempotent summand; the finite distributivity argument is elementary and correctly preserves the differential maps.
- Step 3: checked against `lem-weil-proetale-countable-products-exact` and `def-pc-tensor-complex-sheaves`; finite totalization and exact termwise products give the chain-level isomorphism, with the sign differential respected componentwise.
- Step 4: checked against `def-weil-pbc-derived-inverse-limit` and `def-weil-derived-tensor`; removed the tower-specific product-representation citation, since the item quantifies over an arbitrary family, and retained the termwise exact-product model and naturality argument.
- New nodes: none; therefore B1--B7 and duplicate-node checks are vacuous. Existing dependency statements were opened and their quoted sentences in `citations.json` verified verbatim.
- Edge cases checked: zero terms and zero family members give zero comparisons, a one-term complex is finite distributivity, and identity transitions preserve the map.

Changes made: corrected step 1's representative choice and K-flat justification; corrected step 4's product-model citation and removed the inapplicable proposition dependency; updated `citations.json` accordingly. No statement correction or source error was found.
