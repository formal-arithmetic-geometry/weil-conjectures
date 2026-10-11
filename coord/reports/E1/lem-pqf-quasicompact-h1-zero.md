1. Files written

- `dag/nodes/sec-abelian-varieties/lem-pqf-quasicompact-h1-zero.json`: statement node split into five proof steps.
- `dag/nodes/sec-abelian-varieties/lem-pqf-h1-filtration-ideals.json`: statement-only child; Mathlib searches found no matching theorem.
- `citations.json`: verbatim citations for every non-elementary node used by the item.

2. Attachments

None.

3. WANTED

None. The Stacks source is recorded in the imported literature path and the proof was checked against Tag 01XF.

4. What was wrong or incomplete

The item was unsplit despite being the full proof of Stacks Tag 01XF. Its parent `pqf-lem-serre-criterion` cited it as an external input. I added the missing filtration lemma rather than duplicating existing nodes for closed-subset ideals, closed points, or the affine basic-open criterion.

## Not duplicates

`lem-pqf-h1-filtration-ideals` vs `lem-weil-pbc-derived-functor-long-exact`: the new node specializes a finite filtration with ideal-sheaf subquotients to H^1 vanishing; the existing node states abstract derived-functor long exactness and does not state this implication.

`lem-pqf-h1-filtration-ideals` vs `lem-pqf-quasicompact-h1-zero`: the new node is only the finite-filtration implication H^1(X,I_i)=0 => H^1(X,F)=0; the item additionally assumes quasi-compactness and concludes that X is affine.

`lem-pqf-h1-filtration-ideals` vs `lem-weil-pbc-finite-surjective-affine-target-noetherian`: the new node concerns filtered sheaves and cohomology vanishing on an arbitrary scheme; the existing node concerns affineness of a source under a finite surjective morphism to an affine Noetherian target and does not state filtered H^1 vanishing.

5. What I checked

I read the Tag 01XF statement and proof (the Stacks web rendering, lines 26-48), and compared each item hypothesis with the node: only quasi-compactness and vanishing for all quasi-coherent ideal sheaves are used. Step 1 uses the existing closed-subset ideal statement and spells out the quotient on the affine neighbourhood; Step 2 uses the existing compact/Kolmogorov closed-point statement; Step 3 uses exactly the new finite-filtration statement; Step 4 is the long-exact-sequence consequence of the displayed short exact sequence; Step 5 uses the existing unit-ideal affine criterion. The small cases are consistent: for an affine scheme, take U=X and f=1; for a one-element cover, the kernel filtration has one zero quotient. I also checked that every citation quote in `citations.json` is copied verbatim from its node statement and that no proof step cites a node for content absent from that statement.

## Review by E1

I checked the source and hypotheses line by line against Tag 01XF. The new filtration node is strictly smaller than the item and contains no proof sketch, only its self-contained statement. Existing nodes were opened before citation: `lem-sc-closed-subset-qc-ideal` supplies ideals for closed subsets, `lem-sc-quasi-compact-kolmogorov-closed-point` supplies closed points in nonempty closed subsets, and `lem-weil-pbc-affine-unit-ideal-basic-opens` supplies the final affineness criterion. The filtration step uses only the new node's stated implication. I corrected the imported empty proof by expanding all five source arguments and added the required Mathlib search records, including the unavailable LeanSearch result.

## Second reading by E1

- Step 1 checked against Stacks Tag 01XF and the statements of `lem-sc-closed-subset-qc-ideal`, `lem-weil-pbc-reduced-induced-closed-subscheme`, and `lem-weil-pbc-derived-functor-long-exact`; verdict: repaired with the affine-local quotient calculation and long-exact lifting citation.
- Step 2 checked against Tag 01XF and `lem-sc-quasi-compact-kolmogorov-closed-point`; verdict: agrees.
- Step 3 checked against Tag 01XF and `lem-pqf-h1-filtration-ideals`; verdict: repaired with stalkwise surjectivity and an explicit filtration and quotient identification.
- Step 4 checked against Tag 01XF and `lem-weil-pbc-derived-functor-long-exact`; verdict: agrees.
- Step 5 checked against Tag 01XF and `lem-weil-pbc-affine-unit-ideal-basic-opens`; verdict: agrees.
- `lem-pqf-quasicompact-h1-zero` checked against Tag 01XF statement, including empty and affine cases; verdict: agrees.
- `lem-pqf-h1-filtration-ideals` checked against the finite-filtration paragraph of Tag 01XF; verdict: strict auxiliary implication, statement only.

Changes: added the missing long-exact citation and quote; added the reduced-induced-subscheme citation needed for the affine quotient; expanded Steps 1 and 3; synchronized proof dependencies and tool uses.
