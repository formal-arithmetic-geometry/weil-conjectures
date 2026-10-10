1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-snapper-numerical-polynomial.json` — statement, split proof, and blueprint metadata; no Mathlib match.
- `dag/nodes/sec-abelian-varieties/lem-sc-snapper-support-reduction.json` — statement-only Stacks input; no Mathlib match.
- `citations.json` — verbatim citations for every non-elementary proof-step dependency.

2. Attachments: none.

3. WANTED: Stacks Project `varieties.tex`, Lemma Tag 0BEL (`lemma-numerical-polynomial-from-euler`), proof text for the support reduction and multivariate Snapper induction, for `lem-sc-snapper-numerical-polynomial`. The source checkout is not present in this worker repository, so the proof is reconstructed from the imported Tag 0BEM route and the existing DAG statements.

4. The imported item had no proof and its blueprint location incorrectly described the surrounding Tag 0BEV argument; the source and blueprint fields now point to the Tag 0BEL induction. The proof uses the existing zero-dimensional Euler-characteristic invariance, embedded-point removal, Euler additivity, and regular-section difference statements. The only new node is the support-reduction statement needed to apply the regular-section node whose hypotheses require full support. No existing node with the same support-reduction statement was found by keyword or tag searches. The Mathlib searches found no declaration of the Snapper theorem or this support-reduction fact.

## Not duplicates

lem-sc-snapper-support-reduction vs lem-sc-snapper-numerical-polynomial: the new node only identifies Euler characteristics after replacing a coherent sheaf by its scheme-theoretic support; the existing item asserts polynomiality in several integer twists and does not state this support-reduction equivalence.

## Review by E1

I read the target node, the `sk-prop-av-isogeny` unit, the ancestor blueprint reference, the existing `lem-sc-hilbert-embedded-points`, `lem-sc-hilbert-difference`, `lem-pc-chi-zero-dim-support`, and `lem-pc-euler-additive` statements, and the available source references for Tags 0BEL, 0BEM, 02OL, 02P2, and 0AYT. The target hypotheses are preserved: properness and coherence are used for support reduction and Euler additivity, invertibility supplies exact tensoring, and the degree bound is the support dimension.

Step 1 uses exactly the existing zero-dimensional statement that tensoring by an invertible module preserves Euler characteristic. Step 2 uses the new support-reduction statement, the embedded-point statement's quotient and dimension drop, and Euler additivity's short-exact-sequence formula; each cited statement says the fact used. Step 3 uses the regular-section statement's explicit forward-difference identity and its lower-dimensional cokernel supports; tensoring by the remaining invertible powers preserves the stated hypotheses. Step 4 is the elementary finite-difference integration argument. Step 5 uses Euler additivity again to combine the two polynomial functions. I checked the edge cases `d = 0`, one invertible module, and `r = 0` (the constant Euler characteristic), and the dimension inequalities are only invoked for finite positive support dimension as required by the cited embedded-point statement.

The new support-reduction statement was checked against the Tag 0BEL proof route and searched in the whole DAG by support, closed-immersion, projection-formula, and Euler-characteristic keywords. Its Mathlib searches were run with LeanFinder, Loogle, and Mathlib grep and found no match. The target's Mathlib searches were also rerun with LeanFinder and Loogle in addition to the existing grep search.

## Second reading by E1

- Item statement: checked against Varieties Lemma 33.45.1, Tag 0BEM, hypotheses field, proper scheme, coherent module, invertible modules, and support-dimension bound; corrected the stale Tag 0BEL reference.
- Step 1: checked against Tag 0BEM's zero-dimensional paragraph and `lem-pc-chi-zero-dim-support`; verdict correct.
- Step 2: checked against Tag 0BEM's embedded-point and support reductions, `lem-sc-hilbert-embedded-points`, `lem-weil-pbc-scheme-theoretic-support`, `lem-weil-pbc-closed-immersion-coherent-equivalence`, and `lem-pc-closed-immersion-coherent-cohomology`; verdict correct after replacing the duplicate support node.
- Step 3: checked against Tag 0BEM's regular-meromorphic-section paragraph and `lem-sc-hilbert-difference`; verdict correct.
- Step 4: checked against Tag 0BEM's final finite-difference arithmetic; verdict is the explicitly marked elementary integration argument.
- Step 5: checked against Tag 0BEM's conclusion and `lem-pc-euler-additive`; verdict correct.
- New-node audit: the proposed support-reduction node was searched against the DAG and found duplicative; no new node remains. Existing cited nodes were read and state the facts used.
- Edge cases: checked zero-dimensional support, the empty support, one invertible module, and the zero-coordinate slice used in finite-difference integration.

Changes: removed the duplicate `lem-sc-snapper-support-reduction` node; corrected the source tag and source place to 0BEM; restored the missing properness hypothesis in the statement; rewrote step 2 to cite existing support, pushforward, and cohomology nodes; updated proof dependencies, blueprint metadata, citations, and the split summary.
