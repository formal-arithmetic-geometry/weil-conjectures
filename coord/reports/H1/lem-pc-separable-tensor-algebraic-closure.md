1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-separable-tensor-algebraic-closure.json`: statement, split proof, Mathlib searches, blueprint reference.
- `dag/nodes/sec-picard-framework/lem-pc-separable-polynomial-alg-closed-quotient-product.json`: statement-only child, no Mathlib match.

2. Attachments: none.

3. WANTED: none.

4. The imported item had no proof. I kept its statement and followed the blueprint route through a primitive element, scalar extension, and factorization over the algebraic closure. The missing non-elementary factorization was made a separate statement-only node after searching the DAG, blueprint, source checkout, and Mathlib.

5. Nothing remains unfinished in the split. The repository checking scripts are outside the read-only sandbox; delivery preflight is the remaining validation.

## Review by H1

I read the target node, its chapter and unit, the blueprint ancestor `lem-pc-ample-positive-degree`, and the relevant Stacks passages (Fields 030N and 09GU; Algebra 00U3 and 030U; Varieties 0FD1). Step 1 cites the existing primitive-element, separable-extension, and power-basis statements, whose text supplies exactly the chosen generator, separability, and presentation. Step 2 cites the existing polynomial scalar-extension and tensor-quotient statements, which give the displayed quotient after base change. Step 3 checks that the Bezout identity remains valid coefficientwise and cites the new quotient-product statement for the Chinese-remainder decomposition. Step 4 checks the root/embedding correspondence and the degree count, citing the new node and the existing finite-rank base-change statement. I also searched Mathlib by LeanSearch, LeanFinder/Loogle, and source grep for both the target and the new child; no exact declaration was found. Small cases checked were degree one and a quadratic separable extension, where the product has one and two factors respectively.
