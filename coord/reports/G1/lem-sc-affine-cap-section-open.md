1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-affine-cap-section-open.json` — repaired split with three proof steps; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-affine-cap-section-open-algebra.json` — statement-only affine algebra lemma; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-affine-cap-section-open-dictionary.json` — statement-only affine dictionary lemma; no Mathlib match.

2. Attachments:

- No exact sorry-free slopmaster2 declaration was found for the item or either new node.

3. WANTED:

- None. The cited Stacks sources are present locally.

4. Repairs made:

- Removed the algebra construction, fibre, localization, and gluing arguments from the item. The item now invokes `lem-sc-affine-cap-section-open-algebra` in one step.
- Added `lem-sc-affine-cap-section-open-dictionary` for the affine sheaf/module correspondence, finite-projective rank-one assertion, and the prime-membership criterion; the item cites it together with clause (3) of `lem-weil-pbc-affine-tilde-gamma-adjunction`.
- Defined “invertible R-module” inline in the algebra node and removed its unused symmetric-algebra base-change statement dependency.
- Replaced the false tensor-power claim by direct application of the first clause to `M^{tensor n}` and `t`, using `def-weil-pbc-ample-invertible-module`.
- Removed `lem-weil-pbc-symmetric-algebra-base-change` and `lem-weil-pbc-nonvanishing-section-trivializes` from the item proof dependencies and tool uses; those belong only to the later algebra-node split.

5. What I could not finish:

- Nothing.

## Review by G1

I reread Stacks Properties Lemma 01PV (the affine construction and its identification of the nonvanishing locus) and the positive-power clause, and read Schemes Lemmas 01IA/01IB and Modules Lemma 01CY for the new affine dictionary statement. The algebra node now states its hypothesis explicitly: an invertible R-module is finite projective of rank 1, equivalently locally free of rank 1 on standard opens. Its statement has no proof steps because it is the new unsplit claim; its source and three Mathlib searches are recorded.

For item step 1, `lem-weil-pbc-affine-tilde-gamma-adjunction` supplies the affine tilde/global-sections counit, while `lem-sc-affine-cap-section-open-dictionary` explicitly supplies finite projective rank one and the equivalence `s_p in p N_p` iff `s in pN`; these are exactly the facts used in the translation. Step 2 uses only the algebra node's stated conclusion that `Spec(B)` identifies with `V={p | s not in pN}`, so it is a black-box application and does not repeat that construction. Step 3 uses the definition node's statement that every positive tensor power is invertible, then applies the first clause to that module and the arbitrary section `t`; it no longer asserts that `t` is a power of `s` or that the two loci coincide.

I checked the hypotheses at each step: `U` is affine, the restricted sheaf is invertible, `s` is a section on the affine open, and the tensor-power exponent is positive. I tested the algebra statement on `s=0` (empty locus) and on a basis section (whole spectrum), and checked the dictionary criterion after localization at a prime. `citations.json` quotes the exact clauses used by every step. The returned D1/C3, C4/C1, B3, and E3 points are all reflected in the files above.
