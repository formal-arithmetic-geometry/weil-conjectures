Files written:

- `dag/nodes/sec-picard-framework/lem-sc-smooth-proper-diagonal-pushforward-structure.json`: statement split, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-smooth-proper-diagonal-basechange-upper-shriek.json`: statement-only auxiliary node, no Mathlib match.

Attachments: none.

WANTED: the local repository does not contain the Stacks TeX sources; the proof source is Stacks Project Tag 0E2P (Lemma 48.12.8), with its use of Lemma 48.12.4.

The item was unsplit. I checked its statement against the online Tag 0E2P equation: it assumes a flat proper morphism and right adjoints for the structural map and diagonal, and concludes the diagonal counit identity. The source proof forms the self-product square, uses the identity composite of the diagonal and the projection to identify the composite right adjoint with the identity, and then invokes the base-change formula for the projection right adjoint. The latter is not stated by any existing DAG node, so I created the strictly smaller statement-only node `lem-sc-smooth-proper-diagonal-basechange-upper-shriek`, sourced to the same proof's invocation of Tag 48.12.4. I searched the whole DAG and blueprint for that base-change statement and found no duplicate. The new node introduces all schemes, projections, right adjoints, and derived categories in its own statement.

## Review by M1

I read the item file, the existing statements `lem-pc-noetherian-derived-direct-image-right-adjoint` and `lem-cat-right-adjoint-composition`, and the new base-change node. Step 1 uses the Noetherian right-adjoint statement only for the projection right adjoint b, and uses the categorical composition statement for the canonical identity comparison; those cited statements explicitly provide a right adjoint and pasted-composition/uniqueness isomorphism. The cartesian square and the equality pr_2 after the diagonal are definitions of the displayed fibre product and diagonal, so the evaluation at the structure sheaf is the elementary objectwise consequence of the natural isomorphism. Step 2 uses exactly the new node's stated canonical isomorphism for b(O_X), then functoriality of c and composition of isomorphisms; its quoted sentence is verbatim. The hypotheses (Noetherian, flat, proper, finite-presentation, and quasi-coherent derived categories) were checked against both the item and auxiliary statement. Small cases are consistent: for f=id_S, P=S and both right adjoints are identities; for a finite flat proper map, the identity reduces to the usual diagonal adjunction counit. Mathlib searches were run for the item and auxiliary node with LeanFinder, Loogle, source grep, and LeanSearch; LeanSearch was unavailable and recorded as such.

What was wrong or incomplete: the imported item had no proof steps and omitted the nontrivial base-change lemma used by Tag 0E2P. This split makes that dependency explicit without restating the item's conclusion as a new node.

What could not be finished: no local Stacks source checkout is present, so the source was read from the official online Tag 0E2P page; no Lean compilation is permitted at stage 1.

## Second reading by M1

- Item statement: checked against Stacks Tag 0E2P, Lemma 48.12.8 and Equation 0E2Q; the Noetherian flat proper specialization and diagonal counit conclusion agree, hypothesis by hypothesis.
- Auxiliary node `lem-sc-smooth-proper-diagonal-basechange-upper-shriek`: checked against the cartesian square and the third equality in Tag 0E2P (invoking Lemma 48.12.4); corrected projection orientation to `pr_2` as the pushforward and `pr_1^*` as the pullback.
- Step 1: checked against proof paragraphs 1 and 2 of Tag 0E2P; added proper base-change and finite-type-over-Noetherian facts so that the Noetherian right-adjoint theorem applies to `P`.
- Step 2: checked against proof paragraph 3 and Equation 48.12.8.1; its citation now quotes the corrected auxiliary statement verbatim and yields the displayed `pr_1^*` formula.
- Small cases checked: `f = id_S` gives `P = S` and identity adjoints; a finite flat proper map reduces to the diagonal adjunction counit; empty schemes and zero complexes satisfy the canonical identity vacuously.
- Changed the auxiliary statement and citation from `pr_2^*` to `pr_1^*`, and added the two Noetherianity/base-change dependencies to Step 1 and `proof_deps`; these repairs align the split with the source square and make the adjoint-existence hypotheses explicit.
