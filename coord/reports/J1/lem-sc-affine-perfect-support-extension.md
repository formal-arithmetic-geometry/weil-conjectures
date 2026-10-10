Files written:
- `lem-sc-affine-perfect-support-extension` (statement, split; no Mathlib match).
- `lem-sc-affine-perfect-plus-shift` (statement-only child; no Mathlib match).
- `lem-sc-perfect-into-support-on-T` (statement-only child; no Mathlib match).
- `lem-sc-affine-support-iterated-cones` (statement-only child; no Mathlib match).

Attachments:
- `lem-sc-affine-perfect-map-lift` is the existing DAG node for Stacks Tag 08EH and is cited in the final step.

WANTED: `literature/stacks-project/perfect.tex` is not present in this checkout; I used the synchronized Stacks source at `/home/ubuntu/c1-stacks-review/perfect.tex` for Tags 08EI, 08EJ, and 08EK.

No statement error was found. The imported item had no proof; its source proof uses three genuine auxiliary results (08EI, 08EJ, and the iterated cone construction), so I recorded them as unsplit child nodes rather than hiding them in an elementary step. The existing 08EH node supplies the required map-lifting statement.

## Review by J1

I read Tag 08EK and the adjacent proofs of Tags 08EI and 08EJ in `perfect.tex`. Step 1 records the finite affine description of the closed support. Step 2 cites 08EI for extending `F` after adjoining `F[1]`, and 08EJ for replacing the equations by powers that annihilate the restriction. Step 3 cites the new iterated-cone statement, which is exactly the source's repeated cone construction and its binomial decomposition on `U`. Step 4 applies the existing 08EH statement to the endomorphism that is zero on the desired `F` summand and identity on the other summands; its quoted clause supplies the perfect source, the isomorphism on `U`, and preservation of support, after which the cone gives the claimed restriction. All hypotheses (affine X, quasi-compact U, closed T with quasi-compact complement, and support of F) were checked against the source. I also ran LeanFinder, Loogle, grep, and LeanSearch for the item and each child; the first three found no matching Mathlib theorem and LeanSearch was unavailable.

## Not duplicates

`lem-sc-affine-support-iterated-cones` vs `lem-sc-affine-perfect-support-extension`: the new node is the intermediate cone construction, asserting support and the full binomial shift decomposition for a chosen list of equations; the item asserts existence of a final supported object restricting specifically to `F \\oplus F[1]`.

## Second reading by J1

- Item statement: checked against Stacks Tag 08EK (Lemma 36.13.10), including affine X, quasi-compact U, quasi-compact complement of T, and support; verdict: agrees.
- Step 1: checked against the first paragraph of Tag 08EK; finite principal-open cover and replacement by powers are valid on an affine; verdict: elementary and valid.
- Step 2: checked against Tags 08EI and 08EJ; the power-annihilation lemma applies to the identity of F on U; verdict: cited statements supply the claims.
- Step 3: checked against the cone construction in Tag 08EK; cone perfection, support, and binomial restriction decomposition agree; verdict: valid.
- Step 4: checked against Tag 08EH and the final paragraph of 08EK; the lifted endomorphism and its cone isolate F\\oplus F[1]; verdict: valid.
- `lem-sc-affine-perfect-plus-shift`: checked against Tag 08EI and the zero and field cases; verdict: self-contained and unchanged.
- `lem-sc-perfect-into-support-on-T`: checked against Tag 08EJ and the affine one-term complex case; verdict: support meaning made explicit.
- `lem-sc-affine-support-iterated-cones`: rechecked the small cases s=0, s=1, and s=2. The prior formula was false already at s=0; it is now corrected to multiplicity `binom(s+1,j)` for `0 <= j <= s+1`, with the additional hypothesis that every `g_i` kills `F|_U`.
- Existing `lem-sc-affine-perfect-map-lift`: statement read and matches step 4; no new node needed.

Changes: removed the unrelated proper-over-base definition dependency, made support mean vanishing of all cohomology sheaves off the closed set, corrected the iterated-cone multiplicities and added the annihilation hypothesis, and made Step 4 explicitly cite support of `C'` from the last clause of 08EH and support of `Cone(gamma)` by the elementary two-of-three property for cohomology sheaves. The worker's Mathlib searches were checked; no declaration matches these scheme-level results.
