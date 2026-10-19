1. Files written:
   - `dag/nodes/sec-smooth-purity/lem-fin-projective-generically-finite.json` (item, split; no new nodes).
   - `citations.json` (verbatim citation support for steps 1 and 2).
2. Attachments: none.
3. WANTED: none.
4. The imported proof was a long projective-space section argument and cited Serre vanishing, twisting, proper closed images, and coherent finiteness. Those dependencies do not state the key generic-fibre-to-open-finiteness implication directly. I replaced that route with the existing proper finite-fibre neighbourhood theorem, which packages the same standard argument and is already in the DAG. No statement weakening or hypothesis change was made.
5. Nothing remains unfinished.

## Review by NY
I read the target node, its blueprint proof, the `sk-prop-sf-cbc` unit, and the chapter record. I also read the statements of `lem-pc-projective-base-change`, `def-pc-projective-morphism`, `lem-weil-pbc-finite-type-dim-zero-artinian`, `def-pc-scheme-fibre`, `lem-pc-projective-proper`, and `thm-sc-proper-finite-fibre-finite-neighbourhood`. Step 1 uses base-change stability of projectivity, the definition's finite-type clause, and the existing theorem that a finite-type zero-dimensional scheme has finite discrete underlying space; the fibre node identifies that space with the ordinary fibre over the generic point. Step 2 uses projective-implies-proper and the proper finite-fibre neighbourhood theorem, whose hypotheses match the Noetherian base and finite generic fibre. Step 3 is the elementary fact that an open containing the generic point of a domain's spectrum is nonempty. I checked edge cases: an empty generic fibre is finite, and the resulting generic open is still nonempty because it contains the generic point. The sole cross-unit citation is declared as a tool use because it is the generic proper-fibre theorem, while this unit's projective route supplies the properness and fibre input.

## Second reading by NY

- Item statement: checked against the blueprint source `lem-fin-projective-generically-finite.md`, including the Noetherian-domain, fraction-field, projectivity, zero-dimensional generic fibre, and nonempty-open conclusion; verdict: agrees hypothesis by hypothesis.
- Step 1: checked the fibre-product/projective base-change statement, projective-morphism definition, finite-type definition, dimension-zero finiteness lemma, and fibre definition; verdict: valid. I made the finite-type inference explicit via affine charts and added the omitted base-change and finite-type citations.
- Step 2: checked projective-implies-proper and the Tag 02OH proper finite-fibre neighbourhood theorem; verdict: hypotheses match (Noetherian base, generic point, finite fibre) and conclusion gives finiteness on an open neighbourhood.
- Step 3: checked directly from the generic point belonging to its neighbourhood; verdict: elementary and valid, including the empty generic-fibre case.
- New-node audit: there are no new nodes in this split; all cited nodes are existing DAG statements, and the Mathlib searches in `searches.jsonl` were inspected for recorded queries and verdicts.
- Changes: expanded Step 1 to justify finite type and added citations for `lem-pc-projective-base-change` and `def-weil-finite-type-morphism`; updated `uses` and `proof_deps` accordingly. No statement or hypothesis was changed.
