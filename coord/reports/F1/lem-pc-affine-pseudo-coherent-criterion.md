1. Files written:

   - `dag/nodes/sec-picard-framework/lem-pc-affine-pseudo-coherent-criterion.json`: split statement, no Mathlib match.
   - `dag/nodes/sec-picard-framework/lem-pc-affine-local-derived-map.json`: statement-only unsplit node, no Mathlib match.
   - `dag/nodes/sec-picard-framework/lem-pc-finite-locally-free-refinement.json`: statement-only unsplit node, no Mathlib match.
   - `dag/nodes/sec-picard-framework/lem-pc-ring-pseudo-coherent-localization-glue.json`: statement-only unsplit node, no Mathlib match.

2. Attachments: none. No sorry-free declaration in `WeilConjectures/` states the item exactly.

3. WANTED: none; the Stacks sources are available in `/home/ubuntu/c1-stacks-review` and cited by their repository paths.

4. The imported item had no proof. I checked the complete proof of Stacks Tag 08E7 in `perfect.tex` lines 2223--2260. The direct implication is the affine sheafification of a finite-free model. The converse uses a finite standard-open cover, actual chain-map realization (Tag 08C9), refinement of finite locally free terms to finite free terms (Tag 0BCI), and the ring gluing criterion (Tag 066D), followed by the all-m formulation. Searches of the whole DAG and blueprint found no duplicate child statements. The source uses `E` as the sheaf associated to `M`; the item’s explicit affine derived-equivalence dependency records this identification.

## Review by F1

I read the item source (`perfect.tex`, Tag 08E7) and the source passages for every new node: `cohomology.tex` Tag 08C9 for local realization, `modules.tex` Tag 0BCI for finite-free refinement, and `more-algebra.tex` Tag 066D for localization gluing. Step 1 cites the pseudo-coherence definition and the affine derived equivalence for the sheafification direction. Step 2 cites exactly the local derived-map statement and finite-free refinement statements; its hypotheses are met on the finite standard-open cover of `Spec(A)`. Step 3 quotes the gluing node verbatim and checks the unit-ideal hypothesis from the cover. Step 4 uses only the definition’s equivalence between pseudo-coherence and m-pseudo-coherence for all m, so it is elementary. I tested the statements on the empty complex, a complex concentrated in degree zero, and the one-element cover `D(1)=Spec(A)`. Mathlib searches were run for each node with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such. No corrections to the mathematical statement were needed.

## Second reading by F1

- Item statement: checked against Stacks Tag 08E7, hypothesis by hypothesis; verdict: correct affine equivalence formulation.
- Step 1: checked against the definition and affine derived-equivalence statements; verdict: direct sheafification implication is supported.
- Step 2: checked against Tag 08E7 and Tag 08C9; verdict: local chain-map use is supported, and finite refinement is elementary from finite local freeness.
- Step 3: checked against Tag 066D; verdict: requires the stated m-pseudo-coherent clause, now included.
- Step 4: checked against the all-m characterization in Tags 08E7 and 066D; verdict: elementary passage to the stated equivalence.
- Child lem-pc-affine-local-derived-map: checked against Tag 08C9 and its hypotheses; verdict: self-contained unsplit statement.
- Child lem-pc-ring-pseudo-coherent-localization-glue: checked against Tag 066D; verdict: repaired to include both m-pseudo-coherent and pseudo-coherent clauses.
- Former child lem-pc-finite-locally-free-refinement: checked against Tag 0BCI and the definition of finite locally free; verdict: removed because its conclusion is a finite-intersection argument elementary in Step 2.

Changes: removed the redundant finite-locally-free refinement node, folded its argument into Step 2, and corrected the gluing node and citation to match the m-pseudo-coherent hypothesis actually used.
