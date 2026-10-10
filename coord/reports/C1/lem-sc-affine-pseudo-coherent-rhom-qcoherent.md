1. Files written:

   - `dag/nodes/sec-picard-framework/lem-sc-affine-pseudo-coherent-rhom-qcoherent.json` (item, split)
   - `dag/nodes/sec-picard-framework/lem-sc-affine-projective-complex-derived-hom.json` (statement-only unsplit node, Mathlib generalization only)
   - `citations.json`

2. Attachments: none.

3. WANTED: literature/stacks-project/cohomology.tex and literature/stacks-project/perfect.tex are cited by the imported DAG but are not materialized in this checkout; the proof follows the cited Tag 0GM8 and Tag 0A6H statements.

4. The item had no sorry-free declaration in `WeilConjectures/`, and no blueprint node or existing DAG node stated the same affine bounded-above finite-projective/bounded-below-complex result. The broader node `lem-sc-pseudo-coherent-rhom-qcoherent` was not used because it depends on this item. I added only the missing derived-Hom computation node; it is strictly weaker than the item and carries a statement only.

5. What was checked:

## Review by C1

I read the item, its ancestor `lem-sc-finite-duality`, the imported Tag 0A6H route, and the existing statements of `lem-sc-derived-hom-finite-free-model`, `lem-weil-pbc-spec-module-tilde-sections`, and `lem-weil-pbc-localization-module-exact`. Step 1 uses the new node for exactly its stated bounded-above projective/bounded-below Hom-complex computation; the truncation remark selects a bounded-below representative from the item's bounded-below cohomology hypothesis. Step 2 uses the finite-free Hom-model statement only after refining to principal opens where finite projectives are finite free, and uses the tilde node for localization and restriction compatibility. Step 3 uses the localization-exactness statement to identify localized kernels, images, and cohomology. Step 4 uses the tilde node's explicit quasi-coherence clause and the lower bound from Step 1. I checked the zero complex and a degree-zero finite-free case: the Hom complex and its associated sheaf reduce to the usual affine module Hom, and the claimed negative-degree vanishing is immediate. Mathlib searches were run for the item and new node with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such. No attachment or duplicate was found.

## Not duplicates

`lem-sc-affine-projective-complex-derived-hom` vs `lem-sc-derived-hom-projective-resolution`: the new statement allows an arbitrary bounded-below target complex, whereas the existing node only treats a target module concentrated in degree zero.

`lem-sc-affine-projective-complex-derived-hom` vs `lem-sc-derived-internal-hom-stalk-localization`: the existing node is a scheme-level stalk comparison for a coherent sheaf in degree zero; the new node is a ring-level derived-Hom computation for arbitrary bounded-above projective and bounded-below complexes.

`lem-sc-affine-projective-complex-derived-hom` vs `lem-sc-ext-stalk-localization`: the existing node identifies Ext stalks for coherent sheaves; the new node computes the entire derived Hom complex for a general bounded-below target complex over a ring.

`lem-sc-affine-projective-complex-derived-hom` vs `lem-sc-derived-hom-finite-free-model`: the existing node computes sheaf internal Hom from a bounded-above finite-free sheaf complex, while the new node computes module derived Hom from a bounded-above projective complex with arbitrary bounded-below target.

`lem-sc-affine-projective-complex-derived-hom` vs `lem-sc-bounded-above-finite-free-hom-acyclic`: the existing node is an acyclicity lemma for sheaf Hom applied to a bounded-below acyclic complex; the new node is the derived-category representation theorem for module Hom and includes the bounded-below cohomology conclusion.

`lem-sc-affine-projective-complex-derived-hom` vs `lem-sc-finite-free-internal-hom-exact`: the existing node proves exactness of internal Hom from one finite-free sheaf; the new node concerns a whole bounded-above projective complex and derived Hom against a bounded-below complex.

## Second reading by C1

- Item statement: checked against Stacks Tag 0A6H, clauses (1) and (3)(a), and the affine module-sheaf construction; verdict: correct after explicitly defining termwise associated complexes.
- New node `lem-sc-affine-projective-complex-derived-hom`: checked against Tag 0GM8 case (2), the K-projective declaration, and the zero and degree-zero cases; verdict: strictly smaller statement, no duplicate, Mathlib search log complete.
- Step 1: checked bounded-below replacement against `def-sbc-standard-tstructure-derived-category` and the new node's RHom conclusion; verdict: corrected to cite truncation and spell out the lower-degree bound.
- Step 2: checked principal-open finite-free refinement and identity quasi-isomorphism against Tag 0A6H (3)(a), `lem-sc-derived-hom-finite-free-model`, and module tilde localization; verdict: corrected to state the local model and differential compatibility explicitly.
- Step 3: checked exact localization of kernels, images, and cohomology against `lem-weil-pbc-localization-module-exact`; verdict: valid on principal opens and glues canonically.
- Step 4: checked quasi-coherence and the lower bound against `lem-weil-pbc-spec-module-tilde-sections` and Step 1; verdict: valid.

Changes made: fixed the new-node `created.item` metadata; defined termwise sheaf complexes in the item statement; added the standard t-structure dependency and citation; expanded Steps 1 and 2 to remove implicit truncation, local-model, and differential-compatibility arguments; synchronized `proof_deps` and citations.
