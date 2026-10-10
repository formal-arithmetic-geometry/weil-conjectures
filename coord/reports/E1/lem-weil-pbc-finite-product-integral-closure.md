# Worker report: lem-weil-pbc-finite-product-integral-closure

1. Files written:

   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-product-integral-closure.json`: three-step proof of Stacks Algebra 0CY8 and 0CY9, using the existing Mathlib leaf `def-weil-pbc-integral-closure`. No new node was needed.

2. Attachments: none. Searches in the read-only slopmaster2 `WeilConjectures/` and `Comparator/` for this blueprint id, finite-product integrality, and integral-closure product declarations found no exact theorem. No Lean was written or built.

3. WANTED: none. Stacks `algebra.tex` at `lemma-finite-product-integral` (0CY8) and `lemma-finite-product-integral-closure` (0CY9) was read directly.

4. Stacks 0CY8 says its proof is omitted. The item now gives that proof: projection of a monic equation proves one direction, and multiplying finitely many component monic polynomials by powers of the variable makes a common-degree monic polynomial over the product for the converse. The empty product is covered explicitly. Stacks 0CY9 follows by equality of the integral-element subsets. The original last sentence used “integrally closed in” for arbitrary maps, although the cited definition states it for inclusions; I clarified this clause by requiring the component maps to be injective. This does not alter the unconditional integral-closure equality. The source's last sentence has the same ambiguity. The whole-blueprint searches by finite-product integrality and integral closure found no duplicate statement; this is a tool fact under the normality argument of `lem-weil-pbc-normal-constant-generic`.

5. `python3 tools/review_split.py lem-weil-pbc-finite-product-integral-closure` passes, as does `python3 tools/blueprint_refs.py check lem-weil-pbc-finite-product-integral-closure`. `python3 tools/check_dag.py` reports zero cycles and seven pre-existing unrelated reachability warnings. No part of this item remains unfinished.

## Review by E1

I read Stacks Algebra 0CY8 (lemma-finite-product-integral), whose proof is omitted, 0CY9 (lemma-finite-product-integral-closure), and the intervening definition-integral-closure. The first clause of the item is 0CY9 exactly. The final clause now assumes injective component maps because that source definition says "integrally closed in" only after identifying R as a subring of S; this makes the clause meaningful without altering the unconditional closure equality. The existing def-weil-pbc-integral-closure node defines the monic-polynomial criterion and the closure subring used in all three steps. No new node was created, and whole-DAG and blueprint searches found no duplicate statement or exact sorry-free Lean attachment.

Step 1 projects a monic equation in the product ring to each factor; projection preserves its leading coefficient 1. Step 2 takes finitely many component monic equations, multiplies each by a power of T to a common degree, and assembles their coefficients into one monic product-ring polynomial. That supplies the omitted reverse implication of 0CY8. For an empty index set the product is the zero ring, and T annihilates its sole element, so the edge case is sound. Step 3 identifies the sets of integral elements and hence their subrings; with injective component maps, equality with the image of R is equivalent to equality in each component. All non-elementary input is the cited definition; the polynomial manipulations are explicit. The correction of the ambiguous source wording is reported, and I found no A-E defect requiring worker repair.
