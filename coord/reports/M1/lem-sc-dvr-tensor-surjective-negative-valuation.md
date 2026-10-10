# Delivery report

## Files written

- `dag/nodes/sec-curve-estimates/lem-sc-dvr-tensor-surjective-negative-valuation.json` — item, split.
- `dag/nodes/sec-curve-estimates/lem-sc-dvr-valuation-ring-characterization.json` — statement-only node, Mathlib generalizations found but no exact match.
- `citations.json` — verbatim step citations.

## Attachments

None. No sorry-free declaration in the slopmaster2 source states the item exactly.

## WANTED

None.

## Review by M1

I read the item source, Stacks Varieties Lemma 09N5 (the induction base case), and checked the statement against its hypotheses: A is a subring of K with fraction field K, B is a DVR with fraction field K and normalized valuation, and A tensor B maps surjectively to K. I also read the existing node `lem-sc-dvr-valuation-arithmetic`; its statement explicitly supplies multiplicativity of the valuation, which is the only part used from it. The new characterization node is sourced to Algebra Definition 00IE and states exactly the two DVR facts used: nonzero elements of B have nonnegative valuation, and a uniformizer and its inverse have valuations 1 and -1.

Step 1 uses the new node for the inverse of a uniformizer and then unpacks surjectivity of the canonical tensor map into a finite sum; this is the definition of the tensor product map. Step 2 assumes all nonzero elements of A have nonnegative valuation, combines that hypothesis with the new node for B and the existing arithmetic node for products, and uses closure of B under finite sums to contradict the inverse-uniformizer valuation. Step 3 is the elementary negation of that assumption and selects a nonzero summand coefficient. The hypotheses needed at each step are present in the item statement. I tested the argument on the standard DVR k[t]_(t) with K=k(t): if A=B, the tensor map is not surjective because t^{-1} is absent; if A=k[t,t^{-1}], the conclusion is witnessed by t^{-1}.

I searched the whole DAG and blueprint for the valuation-ring characterization and for the item tag before creating the new node; no duplicate statement or blueprint node was found. I ran LeanFinder, Loogle, grep, and LeanSearch for both the item and the new node. LeanFinder returned only generic valuation declarations, Loogle and grep found no exact bundled statement, and LeanSearch was unavailable (HTTP 500), recorded as such in each node's search log. The item has no matching declaration in either source checkout.

## What was wrong or incomplete

The imported item had no proof and therefore omitted the finite tensor expansion and the valuation-ring facts needed for the contradiction. I supplied those steps and added the missing statement-only interface; no source error was found.

## What could not be finished

Nothing blocking the delivery.
