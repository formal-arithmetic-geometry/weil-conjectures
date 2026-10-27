## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-field-product-square-power.json`: split item with a three-step proof; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-field-square-after-finite-extension.json`: new statement-only intermediate node for Guo Claim 5.2.1; no Mathlib match.
- `citations.json`: verbatim citations for the proof steps.

## Attachments

- `lem-sfb-finite-field-picard-norm-base-change` is an existing split node used for finite-extension Picard norm descent.

## WANTED:

- `literature/guo-divisors-coherent-schemes-homogeneous-spaces.pdf`, local copy of the online March 31, 2026 author version, for Proposition 5.2(ii) and Claim 5.2.1.

## What I checked and corrected

The imported item cites Guo Proposition 5.2(ii) but had no proof. The source defines the square difference on (W\times_S W\times_S X_3), and its field-case proof first establishes Claim 5.2.1 after a finite extension and then descends by the norm. I retained the item's smooth separated finite-presentation and geometric-integrality hypotheses and added only the intermediate finite-extension square node. I did not use the unrelated SGA 4 trace route.

## Review by Q28

I read the item and the unit/chapter records, the current Guo PDF through Proposition 5.2(ii), Claim 5.2.1 and the norm paragraph (printed pp. 11–12), the existing DAG node `lem-sfb-finite-field-picard-norm-base-change`, and the relevant tensor/pullback definitions. Step 1 cites the new node, whose statement gives exactly the finite extension (K/k), the invertible (N_K), and the isomorphism (D(A_K)\cong\pi_K^*N_K) used there. Step 2 cites the existing norm node: its statement supplies multiplicativity, the degree-(d) identity for pullbacks, and arbitrary pullback compatibility; the remaining identification of the four-term square difference after base change and the identity (D(A^{\otimes d})\cong D(A)^{\otimes d}) are direct expansions of the definitions. Step 3 applies the same norm pullback compatibility to (pi), then uses the degree identity and the tensor expansion to choose (n=d\ge1) and (N=\operatorname{Nm}(N_K)). I verified the hypotheses of the norm node (a finite field extension and invertible modules on the two schemes) and checked the edge case (d=1), where the norm is the identity. The Mathlib searches for the new node were run with LeanFinder, Loogle, grep, and LeanSearch; their returned declarations concern pullback carriers, tensor algebra, or finite-field quadratic squares and do not state this geometric theorem. Whole-DAG and blueprint searches found no duplicate or blueprint node for the finite-extension square claim.
