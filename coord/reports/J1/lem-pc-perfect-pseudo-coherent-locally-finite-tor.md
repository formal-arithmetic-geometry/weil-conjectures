1. Files written:

   - `dag/nodes/sec-picard-framework/lem-pc-perfect-pseudo-coherent-locally-finite-tor.json` — statement, two-step proof, Mathlib searches, status `split`; no new child nodes.
   - `citations.json` — verbatim citations for every step/node use.

2. Attachments: none.

3. WANTED: none.

4. The imported node had no proof. I checked the item against Stacks Cohomology of Sheaves, Lemma 08CQ, implication (1) => (2), and against the project definitions `def-pc-perfect-complex` and `def-pur-pseudo-coherent-complex`. Step 1 uses exactly the local strictly-perfect model and the bounded-above finite-free definition, so it is elementary once those statements are in hand. Step 2 uses the same local cover; its terms are flat direct summands of finite free modules, and the existing `lem-pc-bounded-above-flat-kflat` states that the bounded-above flat complex is K-flat. The ordinary tensor with any module is therefore represented by a bounded complex, giving a uniform finite degree interval on each open. I checked the hypotheses and the direction of the implication in both cited node files. No duplicate child node was created: the two arguments are direct steps from the definition and the existing K-flat lemma.

5. I could not find a matching sorry-free Lean declaration. The required LeanFinder, Loogle, grep, and LeanSearch queries found no scheme-level Mathlib theorem; LeanSearch was unavailable.

## Review by J1

I read the item file, the chapter and unit records, the source definition of perfect complexes, the pseudo-coherence definition, the existing bounded-above-flat K-flat node, and the Stacks 08CQ proof. I verified that the perfectness cover supplies the same open neighborhoods used in both conclusions, that the local complexes are bounded, and that their terms are direct summands of finite free modules. I corrected the item by replacing its empty proof with the two source-aligned steps, adding the K-flat dependency only where the derived-to-ordinary tensor passage occurs, recording all searches actually run, and adding exact citation quotes. The blueprint search found no alternate statement and no new node was needed.

## Second reading by J1

- Item statement: checked against Cohomology of Sheaves, Lemma 08CQ (cohomology-lemma-perfect), implication (1) => (2); the scheme specialization and pointwise local Tor-amplitude formulation agree hypothesis by hypothesis.
- Step 1: checked against Definitions 08CM/08C4 and affine comparison 08EB, plus the existing finite-projective standard-free-cover node; principal-open refinement supplies the local finite-free pseudo-coherence condition.
- Step 2: checked against the 08CQ proof and lem-pc-bounded-above-flat-kflat; direct-summand terms are flat, K-flatness identifies derived and ordinary tensor, and boundedness gives a module-independent interval.
- New nodes: none; the existing module-cover node was searched and cited instead of duplicated.
- Small cases: zero and field cases are immediate, the empty scheme is vacuous, and the interval permits a=b.
- Changes: corrected Step 1's false same-open finite-free claim; added affine refinement and principal-open intersections, the node to `uses`/`proof_deps`/`tool_uses`, and its verbatim citation.
