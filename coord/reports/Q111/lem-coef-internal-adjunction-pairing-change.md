Files written:

- `dag/nodes/sec-six-functors/lem-coef-internal-adjunction-pairing-change.json` — repaired the item split into eight explicit steps; no new nodes, no Mathlib leaves.
- `citations.json` — twelve verbatim citations for the repaired steps.
- `report.md` — this repair report.

Attachments: none. No declaration in the read-only source trees carries the item tag or states the displayed equality without `sorry`.

WANTED: none.

The returned split failed because its first, second, and fourth steps asserted coefficient compatibility of the compact-support projection without displaying the open/proper squares or computing their common transposes. Its third step also cited `lem-coef-finite-closed-shriek`, whose statement is on pro-etale exceptional inverse images, while the item is on ordinary etale categories and already assumes the required counit equation. I removed that proof and statement dependency. The item statement and its hypotheses are unchanged. The repaired proof now separates the open projection square, the proper projection square, their pasted compact-support square, the assumed exceptional-counit equation, the evaluation comparison, the full left-hand transpose computation, the right-hand transpose computation, and the final Hom-bijection argument.

## Review by Q111

I reread the item statement, its source paragraph in `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md`, and the current statements of `lem-coef-etale-open-tensor`, `lem-coef-finite-direct-image`, `lem-sfb-dc-hom-scalar-adjunction`, and `lem-asd-internal-adjunction-evaluation`. The finite-field and coefficient hypotheses, the ordinary etale categories, the locally closed factorization (s=gj), the finite-Tor assumptions on (N,Q), and the definitions of (c,q,b,u,v) remain exactly those of the item.

Step 1 uses the open-tensor statement that γ is the (j_!\dashv j^*) adjunct and that (q_{j,P}) restricts to the identity. I checked the adjuncts have the same restriction/tensor map, which proves the open constituent square. Step 2 uses the direct-image statement that (c_{g,Q}) is defined by the coefficient-counit transpose and is the projection map followed by the restriction/direct-image comparison; I explicitly compare the two proper projection routes after the inverse-image/direct-image tensor-Hom adjunction, so their transposes are the same. Step 3 pastes these two actual squares and states the resulting compact-support projection equality, including tensor reassociation. The direct-image composition clause and the open comparison's associativity clause are the cited coherence facts.

Step 4 uses only the displayed hypothesis εₛ,B ∘ s!,B(bₛ,M) ∘ qₛ,N = Fₓ(εₛ,A), so no pro-etale exceptional theorem is being applied to the ordinary etale setting. Step 5 uses the evaluation normalization in the scalar internal-Hom node to identify the transpose of (u) with coefficient change of εᴀ. Steps 6 and 7 use the explicit transpose formula in `lem-asd-internal-adjunction-evaluation` and the evaluation normalization of scalar internal Hom: Step 6 writes the complete left-hand chain through (c), (q), the B projection, (u), (b), and εₛ,B; Steps 3–5 replace each segment by the coefficient change of the corresponding A segment. Step 7 computes the right-hand transpose from the A projection, evaluation, and εₛ,A, followed by (F_X) and (v). Step 8 invokes the representing Hom-bijection stated by the scalar-adjunction node to conclude equality from equality of transposes.

I checked every citation quote against the current node statement after the repair; all twelve are verbatim substrings, and no citation points to the removed closed-shriek theorem. Every proof step is below 2000 characters. The edge cases (m=n) and (m=1) reduce respectively to identity coefficient comparisons and the first quotient comparison; the square and transpose calculations remain valid in both cases. No new node, statement change, dependency cycle, SGA citation, Lean file, compiler, or Lake/build command was introduced.
