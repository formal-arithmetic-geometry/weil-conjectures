1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-perfect-cut-complex-degree-zero.json`: split item with three proof steps.
- `dag/nodes/sec-abelian-varieties/lem-pc-affine-perfect-cut-degree-zero.json`: statement-only affine lemma, no Mathlib match.
- `citations.json`: verbatim citations for both non-elementary steps.

2. Attachments: none.

3. WANTED: none.

4. The item has no project declaration in the Lean source and no sorry-free attachment. Its source is Stacks Tag 0A1U, whose affine proof uses finite-free models, basis choices after localization, finite-projective cokernel, and splitting of the truncation triangle. I kept the item's scheme-level statement and introduced only the strictly smaller affine ring lemma that carries that algebraic argument. Searches of the DAG and blueprint found no existing node for this affine cut statement; the existing finite-free residue model node is a different, more general local-model result and is cited rather than duplicated.

## Not duplicates

`lem-pc-affine-perfect-cut-degree-zero` vs `lem-sc-perfect-finite-free-residue-model`: the new node is an affine truncation splitting under a surjective degree-zero fibre map, while the existing node only constructs a finite-free local model with prescribed fibre ranks.

`lem-pc-affine-perfect-cut-degree-zero` vs `lem-sc-perfect-cut-complex-degree-zero`: the new node is the ring-local algebraic lemma for a bounded-above finite-free complex at one prime, while the item is the scheme-level perfect-complex conclusion on an open neighbourhood; the item uses the affine lemma as its substantive proof step.

## Review by J1

I read the full proof of Stacks Tag 0A1U in `more-algebra.tex` and checked the item hypotheses against it. Step 1 cites the existing Tag 0BCD finite-free residue-model statement; Tor-amplitude [0,infinity) makes the negative residue ranks zero, so the chosen complex is concentrated in nonnegative degrees. Step 2 cites the new affine statement, which exactly supplies the localization, truncation splitting, and positive Tor-amplitude conclusion; its statement includes the prime, bounded-above finite-free complex, and surjectivity hypotheses used in the source. Step 3 is elementary truncation bookkeeping: with no negative cohomology, the nonpositive truncation is H^0 in degree zero, and the positive truncation is the required P.

I tested the statement on the zero complex, a complex concentrated in degree zero over a field, and a split complex R in degree zero direct-sum R[1]; all give the asserted local splitting. The affine lemma is not in Mathlib: LeanFinder returned only generic homological splitting/localization declarations, Loogle and Mathlib grep found no matching truncation theorem, and LeanSearch was unavailable; those exact searches and verdicts are recorded in its node. The item searches likewise found no scheme-level match. The citation quotes are copied verbatim from the cited node statements, and the only new node is strictly below the item.

5. What remains: the second worker should re-read this split and run the dry run.

## Second reading by J1

- Item statement: checked against Stacks Tag 0A1U (Lemma `better-cut-complex-in-two`) in `more-algebra.tex`, lines 19743-19763; the added perfect/Tor-amplitude hypotheses specialize the pseudo-coherent source lemma to the stated application, and the nonnegative amplitude identifies the nonpositive truncation with H^0.
- Step 1: checked against Tag 0BCD and Tag 0A1U; the finite-free residue model supplies the bounded finite-free representative, and vanishing negative fibre cohomology follows from the stated Tor-amplitude hypothesis.
- Step 2: checked against the complete Tag 0A1U proof and the statement of `lem-pc-affine-perfect-cut-degree-zero`; the step now uses only the node's stated localization, splitting, and positive-truncation conclusion, rather than relying on details hidden in its proof.
- Step 3: checked against the truncation triangle used in Tag 0A1U; with no negative cohomology, `tau_{<=0}` is H^0 in degree zero, and the remaining summand retains the node's perfectness and amplitude.
- `lem-pc-affine-perfect-cut-degree-zero`: statement-only B1-B7 check completed; self-contained ring, prime, bounded-above finite-free complex, fibre map, localization, and truncation notions are stated, and searches in the DAG and Mathlib search log found no duplicate or Mathlib declaration. Tested on the zero complex, a field concentrated in degree zero, and a split degree-zero plus degree-one complex.

Changes made: corrected the item node's `created.item` metadata to this delivered item; removed an accidental self-reference from the affine node's blueprint `via`; and rewrote step 2 to cite only the affine node statement, eliminating an E/C3 proof-interface defect.
