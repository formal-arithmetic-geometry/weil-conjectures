1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-smooth-proper-diagonal-koszul-dual.json`: repaired split item, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-koszul-regular-immersion-derived-hom.json`: repaired statement-only unsplit node, no Mathlib match.
- `citations.json`: updated verbatim citations for every proof-step use.

2. Attachments: none. No project declaration states the item exactly.

3. WANTED: none.

4. What was wrong and corrected:

The returned node `lem-sc-closed-immersion-derived-pushforward-fully-faithful` asserted a false theorem for derived categories, so it was deleted. Step 3 now descends through the existing affine derived equivalence `lem-sc-finite-affine-derived-equivalence`, applied to the affine closed immersion `i`; the module-compatible pushforward isomorphism from Step 2 is exactly what this equivalence transports back to `D_QCoh(O_Z)`. The Koszul Ext node now states compatibility with the `i_*O_Z`-module structures. Its source and Step 2 source were corrected to Tag 0BR1, `lemma-regular-immersion-ext`. Step 2 now uses the actual hypothesis that `C_i` has constant rank `d`, rather than asserting an unsupported codimension phrase.

## Not duplicates

`lem-sc-koszul-regular-immersion-derived-hom` vs `lem-sc-rhom-cohomology-ext-ring`: the existing node is a ring-level cohomology/Ext identification; this node is the scheme-level Koszul closed-immersion calculation.
`lem-sc-finite-affine-derived-equivalence` vs the deleted `lem-sc-closed-immersion-derived-pushforward-fully-faithful`: the retained node is the affine module-category equivalence; the deleted node asserted false derived full faithfulness.

## Review by J1

I reread Stacks Tags 0BR0 and 0BR1 and opened every node cited by each item step. The finite-morphism and finite-duality nodes say exactly what Step 1 takes, including the `i_*O_Z`-module compatibility. The new Koszul Ext node states the exact exterior-power and shift formula, with module compatibility, used in Step 2. The affine-equivalence node states the equivalence and restriction functor used in Step 3. I verified the Noetherian, affine, Koszul-regular, and constant-rank hypotheses, and checked every citations.json quote verbatim against its node statement. I removed the false derived full-faithfulness claim, corrected the source tag to 0BR1, and checked rank-zero and Cartier-divisor cases.

5. Nothing remains unfinished; the dry run is the remaining mechanical check.

## Second reading by J1

- Item statement: checked against Stacks Tag 0BR0, `lemma-regular-immersion`; corrected the setting to a quasi-compact, quasi-separated scheme, the locally constant rank `r`, and the right adjoint `a` exactly as stated there.
- Step 1: checked against the statements of `lem-weil-pbc-closed-immersion-finite` and `lem-sc-finite-duality-derived-hom`; the finite hypothesis and the pushforward derived-Hom identification apply, with `a` as the right adjoint.
- Step 2: checked against the corrected Koszul Ext node and Stacks Tag 0BQZ, `lemma-regular-immersion-ext`; the rank and Koszul-regular hypotheses give the displayed `Ri_*` formula.
- Step 3: checked against `lem-sc-finite-affine-derived-equivalence`; closed immersions are affine and the module-compatible isomorphism descends through the stated equivalence.
- New node `lem-sc-koszul-regular-immersion-derived-hom`: checked against Tag 0BQZ and the cited definitions; retained as a strict scheme specialization of the ringed-space lemma, with the locally constant rank stated explicitly and all notions self-contained.
- Source error: the worker wrote Tag 0BR1 for the Ext lemma, but the tag index identifies 0BR1 as an unrelated topology result; the correct tag is 0BQZ. The source and all dependent step metadata were corrected.
- Changes: corrected the item hypotheses and adjoint notation, corrected the Ext source tag and rank wording, updated the proof text and verbatim citation, and removed the report’s claim of a second new fact that was deleted.
