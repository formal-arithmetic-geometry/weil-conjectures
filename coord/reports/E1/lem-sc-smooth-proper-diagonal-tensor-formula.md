1. Files written:
   - item `lem-sc-smooth-proper-diagonal-tensor-formula` (repaired split)
   - `lem-sc-smooth-proper-tensor-direct-sums` (statement-only, no Mathlib match)
   - `lem-sc-smooth-proper-tensor-perfect-case` (statement-only, no Mathlib match)
   - `citations.json`
2. Attachments: none.
3. WANTED: `literature/stacks-project/duality.tex`, Tags 0A9R, 0A9T and 0A9U; the local checkout has only citation indexes.
4. The return correctly identified that the prior proof simply invoked 0A9U. I replaced it with the requested route: direct-sum preservation, the exact saturated triangulated subcategory, compact generation and existence of c, the perfect case, and the localizing-subcategory conclusion. The statement now defines the canonical comparison as the adjunction mate. Both new statements were searched in the DAG, blueprint and Lean/Mathlib search services; no existing declaration or Mathlib theorem states them.

## Review by E1

I read the returned item, its blueprint ancestor, and the existing compact-generation and right-adjoint nodes. Step 1 uses exactly the new direct-sums statement. Step 2 uses that statement for closure under sums and spells out exactness and saturation. Step 3 quotes the existing compact-generation and right-adjoint statements, whose hypotheses supply the Noetherian quasi-coherent setting. Step 4 uses exactly the new perfect-case statement. Step 5 applies the localizing-subcategory argument and reverses the comparison isomorphism. I checked every citation quote against the node text and recorded it in `citations.json`. The comparison morphism is defined in the item statement, and the closed-immersion, Noetherian, proper and local-perfect hypotheses were retained.

## Second reading by E1

- Item statement: checked against Stacks Tag 0A9U and the displayed comparison map; the closed-immersion specialization, properness, perfectness, Noetherian hypotheses, and mate orientation are retained.
- Step 1: checked against Tag 0A9R; the direct-sums node supplies exactly the conclusion and now defines the derived categories and derived direct image it uses.
- Step 2: checked against the natural-transformation argument in Tag 0A9U; exactness gives shifts and cones, retracts are preserved, and step 1 supplies arbitrary sums.
- Step 3: checked against the Tag 0A9U generator argument and the right-adjoint node; the perfect-generation node supplies the needed generators and the adjoint node applies to the closed immersion.
- Step 4: checked against Tag 0A9T; the perfect-case node has matching perfect, proper, Noetherian, adjunction, and derived-category hypotheses.
- Step 5: checked against the final paragraph of Tag 0A9U and the P-resolution remark; it now cites perfect generation and direct-sum closure and explicitly derives the localizing-subcategory conclusion.
- `lem-sc-smooth-proper-tensor-direct-sums`: checked statement against Tag 0A9R; added explicit derived direct-image and derived-category definition citations.
- `lem-sc-smooth-proper-tensor-perfect-case`: checked statement against Tag 0A9T; added explicit derived direct-image definition citation.
- `lem-pc-derived-qcoh-perfect-generation`: checked statement against Theorem `perfect-theorem-bondal-van-den-Bergh`; no Mathlib scheme-level match after leanfinder, Loogle, and grep searches.

Changes: added the missing definition dependencies to both auxiliary nodes; added the perfect-generation statement because compact generation alone did not justify the perfect-case reduction; rewrote steps 3 and 5 and updated verbatim citation quotes accordingly.
