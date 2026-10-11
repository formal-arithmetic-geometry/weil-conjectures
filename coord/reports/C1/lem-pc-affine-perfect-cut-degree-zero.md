1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-pc-affine-perfect-cut-degree-zero.json`: statement split into three proof steps; Mathlib searches found no exact match.
- `dag/nodes/sec-abelian-varieties/lem-pc-finite-projective-cokernel-localization.json`: statement-only Tag 00O0 input; Mathlib searches found no exact match.
- `dag/nodes/sec-abelian-varieties/lem-pc-derived-splitting-unique.json`: statement-only Tag 0BCG input; Mathlib searches found no exact match.
- `citations.json`: verbatim citations for the two non-elementary proof steps.

2. Attachments: none.

3. WANTED: none; the relevant Stacks source is available in the local review checkout at `/home/ubuntu/c1-stacks-review/more-algebra.tex` and `/home/ubuntu/c1-stacks-review/algebra.tex`.

4. The imported item had no proof. I checked Tag 0A1U in full and followed its proof: the degree-zero fibre surjectivity is used to lift a basis of the quotient of cycles by boundaries; the localization step is exactly the finite-projective cokernel criterion of Tag 00O0; the final direct sum is the truncation triangle split from Tag 0BCG. The existing broader node `lem-sc-perfect-cut-complex-degree-zero` was not cited because its proof already depends on this affine item, which would create a cycle.

## Review by C1

I read Tag 0A1U (Lemma better-cut-complex-in-two), Tag 00O0 (Lemma cokernel-flat), and Tag 0BCG (Lemma splitting-unique). The item statement matches Tag 0A1U at i=0 after specializing its pseudo-coherent complex to the stated bounded-above finite-free complex. Step 1 is the elementary vector-space construction in the source: V is the image, W is the kernel, the assumed surjection supplies representatives for W/V, and the chosen complement gives linearly independent d^0(z_c). Step 2 cites the exact clause of the new 00O0 node and uses it to obtain the basis/cokernel localization and the bounded finite-projective model of the positive truncation. Step 3 cites the exact splitting clause of the new 0BCG node and checks its hypotheses with a=1: the positive truncation has projective amplitude beginning in degree 1 and the nonpositive truncation has no cohomology above degree 0. I tested the construction on the zero complex and on a two-term complex with d^{-1}=0, d^0 an inclusion of a direct summand; both give f=1 and the asserted decomposition. Both new nodes are statement-only, have complete hypotheses, source tags, blueprint ancestry, and recorded searches (LeanSearch was unavailable and recorded as such). `citations.json` quotes the precise clauses used by Steps 2 and 3.

## Not duplicates

lem-pc-finite-projective-cokernel-localization vs lem-pc-hilb-representable: the latter is a Hilbert-scheme representability theorem whose incidental citation text contains tag 00O0; it does not state any finite-projective map or cokernel localization result.

lem-pc-finite-projective-cokernel-localization vs lem-sc-finite-locally-free-residue-isomorphism: the existing node states that a morphism of finite locally free sheaves is an isomorphism when every fibre map is an isomorphism (Tag 00O0 part (3)); the new node is the distinct injective-fibre criterion yielding a localized injective map and finite-projective cokernel (Tag 00O0 part (1)).

## Second reading by C1

- Item statement: checked against More on Algebra Tag 0A1U, including the bounded-above finite-free specialization at degree zero, the surjective fibre hypothesis, localization away from the prime, and the truncation/direct-sum conclusion; verdict: mathematically consistent.
- Step 1: checked the definitions of the residue-field image and kernel and the basis lifting argument in the proof of Tag 0A1U; verdict: elementary and valid.
- Step 2: checked against Tag 0A1U and Algebra Tag 00O0 parts (1) and (3); verdict: repaired to use the residue-isomorphism clause for the degree-zero basis map and the injective-fibre clause for the selected differential and its finite-projective cokernel.
- Step 3: checked against More on Algebra Tag 0BCG parts (1)--(3) and the canonical truncation triangle; verdict: hypotheses match with a=1 and the splitting conclusion is valid.
- New node lem-pc-finite-projective-cokernel-localization: checked against Tag 00O0 parts (1) and (3), including the prime, residue-field, localization, injectivity, isomorphism, and finite-projective-cokernel clauses; verdict: repaired to state both clauses and define finite projective as a finite-free direct summand.
- New node lem-pc-derived-splitting-unique: checked against Tag 0BCG, hypothesis by hypothesis; verdict: repaired to state the derived category and bounded projective representative explicitly.
- Edge cases checked: the zero complex, a field, the zero ring map at a prime, and a two-term split inclusion; all give the asserted localization and decomposition.
- Changes made: corrected the helper node's source to Tag 00O0 parts (1) and (3), added the missing isomorphism localization clause, rewrote Step 2 to apply both clauses, and made the helper and splitting statements self-contained.
