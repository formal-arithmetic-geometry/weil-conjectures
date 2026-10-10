# Stage 1 report: `lem-weil-pbc-etale-retraction-finite-type-splitting`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-retraction-finite-type-splitting.json`: split into four steps following Stacks 04GG (8) => (11).
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-type-etale-finite-factor-decomposition.json`: new unsplit statement node for Stacks 00UK in the finite type case; no Mathlib match after LeanSearch, Loogle, and source grep.
- `coord/reports/E1/lem-weil-pbc-etale-retraction-finite-type-splitting.md`: this report.

## Attachments

None. The item has no Lean declaration on either source branch.

## WANTED

None. The proof follows the obtained Stacks Project source, `algebra.tex`, Lemmas 04GG and 00UK.

## Findings and changes

The item statement is faithful to condition (11) of Stacks 04GG and was unchanged. The proof has four steps: the finite type 00UK decomposition after an elementary etale extension; the retraction supplied by condition (8); tensoring the decomposition back along the retraction, including finiteness of the first factor; and the closed-fibre isomorphism proving that the second factor has no quasi-finite point over the maximal ideal.

The last point is omitted in the Stacks proof. Explicitly, `tau^{-1}(m)=m'` and the residue-field isomorphism identify `B tensor_R kappa(m)` with `B' tensor_R' kappa(m')`; quasi-finiteness at a prime is isolatedness of the corresponding fibre point, so the property transfers. This uses only the public statement of the new 00UK node and the cited definition.

The Stacks text prints `m = tau^{-1}(m')`, which is ill-typed for `tau : R' -> R`; the proof uses the correct condition `tau^{-1}(m)=m'`. No cited node was used beyond what its statement provides, and the new 00UK node is strictly smaller than the item because it assumes no retraction and asserts only the etale-local decomposition.

## Could not finish

The new 00UK node remains intentionally unsplit and joins the Stage 1 queue. No Lean was written or built.

## Review by E1

I read Algebra Lemma 04GG, implication (8) to (11), and Lemma 00UK. The parent statement retains the local retraction hypothesis and the finite-type map; the new child states the 00UK etale-local finite-factor decomposition, with the finite factors combined into one finite algebra. Step 1 cites that exact child. Step 2 applies the parent's retraction hypothesis to the elementary etale extension; the correct prime condition is $\tau^{-1}(\mathfrak m)=\mathfrak m'$, since $\tau:R'\to R$. Step 3 uses tensor associativity and orthogonal idempotents to preserve the two-factor product, and finite generators base change to finite generators. Step 4 identifies the closed fibres using the residue-field isomorphism and the retraction, so isolated fibre points, hence quasi-finiteness at primes over the maximal ideal, correspond exactly. I checked the case where the finite factor is zero and the case $R'=R$, $\tau=1$. The child is self-contained, statement-only, has exact tag/label citation, and three Mathlib search kinds; I searched 00UK and the factor-decomposition phrase in the current DAG and found no exact prior node. The delivery has only item, child, and report in one commit; it does not change a target or route. No correction was sent back.
