# Stage-1 worker report: lem-trf-local-top-degree-tensor

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-local-top-degree-tensor.json`: retained the statement and split its proof into four steps; no new DAG nodes or Mathlib leaves.
- `citations.json`: literal statement quotations for every cited node in each proof step.
- `searches.jsonl`: retained the required Mathlib search records produced by `msearch.py`.

## Attachments

None. I searched the read-only `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` tree for the exact item id, top-degree tensor terminology, bounded-above finite-free complexes, and likely declaration names. No sorry-free project declaration states the complete item. Generic Mathlib total-complex declarations do not state this top-degree cohomology isomorphism.

## WANTED

None. The direct-sum total-complex convention and tensor right exactness source are available locally.

## What was checked and corrected

The imported statement is mathematically correct and unchanged. Its hypotheses allow zero complexes and arbitrary integers `a,b`; the proof uses only the stated vanishing above those bounds. The seeded node had no proof, so I supplied the direct top-degree quotient argument and added the existing right-exactness node to `proof_deps`. No definition or auxiliary theorem was created.

The whole DAG and blueprint were searched for a top-degree tensor/cohomology statement; the only relevant existing algebraic input is `lem-weil-pbc-tensor-right-exact`, a Mathlib-backed leaf. The blueprint search for “top-degree tensor” returned no duplicate node. The item keeps its inherited ancestor chain and now records the precise complete-local top-cohomology clause as `blueprint.from.place`.

## Not duplicates

No new nodes were created, so there are no new/existing duplicate pairs.

## Review by Q71

I read the complete item statement, its chapter `sec-trace-formula`, unit `sk-i-curve-zero`, the ancestor `lem-trf-local-term-locality`, and the full statements of `def-pc-cochain-complex-modules`, `def-pc-tensor-complex-sheaves`, and `lem-weil-pbc-tensor-right-exact`. I also read the direct-sum tensor convention in `literature/stacks-project/more-algebra.tex` and the Mathlib-backed right-exactness source recorded by the cited leaf. No Lean attachment exists, and no SGA source or coefficient-category identification is involved.

Step 1 uses the cochain-complex definition for integer degrees and the total-tensor statement that degree `n` is the direct sum over `p+q=n` with differential `d_P tensor 1 + (-1)^p 1 tensor d_Q`. Since `p<=a` and `q<=b`, the top degree has only `(a,b)` and the outgoing differential is zero. These are direct substitutions into the cited definitions and are elementary.

Step 2 uses the same total-complex statement. The incoming differential has exactly the two summands from `(a-1,b)` and `(a,b-1)`, with the second sign `(-1)^a`; its image is therefore the sum of the two displayed boundary images, and the sign does not change a submodule. Because the outgoing maps vanish, the top cohomology is the quotient by that sum. This is an elementary degree calculation, with no hidden boundedness assumption.

Step 3 uses the full statement of `lem-weil-pbc-tensor-right-exact`, which says that tensoring an exact sequence ending in a surjection remains exact on the right in either tensor order. Applying it to the two image-to-top-term quotient sequences identifies the successive quotient first with `H^a(P) tensor Q^b` and then with `H^a(P) tensor H^b(Q)`. The cited node states exactly the exactness used; it does not assert flatness or injectivity that the argument would not have.

Step 4 uses functoriality and the representative description in `def-pc-tensor-complex-sheaves`. A pure tensor of top-degree representatives maps to its class in the quotient, so the canonical map in the item is exactly the quotient isomorphism from Step 3. This is elementary once the quotient has been identified.

I checked edge cases `P=0`, `Q=0`, `a` or `b` at any integer, and complexes concentrated in the top degree; the formula gives the expected zero or ordinary module tensor. I also checked that no claim is made about products in total degree (the definition uses direct sums), and every proof step is below 2000 characters. Every non-elementary fact is cited, every citation quote is a verbatim substring of its node statement, and `proof_deps` is exactly the union of the step uses. No statement clause was moved into a child node or weakened to make it provable.

## Unfinished work

None for this one-level split. The sandbox is ready for the required server dry run and delivery.
