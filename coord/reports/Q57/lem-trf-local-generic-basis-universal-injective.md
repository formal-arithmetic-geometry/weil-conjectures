1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-local-generic-basis-universal-injective.json` — statement, split; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-local-fibres-integral-projective.json` — statement-only auxiliary lemma; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-local-universal-injective-residue.json` — statement-only auxiliary lemma; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-local-universal-injective-localization.json` — statement-only auxiliary lemma; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-local-ui-flat-cokernel.json` — statement-only auxiliary lemma; no Mathlib match.
- `citations.json` — verbatim statement quotes for every citation.

2. Attachments: none.

3. WANTED: none.

4. The imported item is the forward implication (1)⇒(2) of Stacks Tag 05I3. I read the complete Tag 05I3 proof in `literature/stacks-project/flat.tex`, including the paragraph that uses Tags 05FQ and 05FT, and the Algebra statements 05CJ, 05CM and 058P. The item statement matches the source and was not weakened or changed. Searches through the DAG found no existing nodes for these four auxiliary statements; the only related node is the parent global free-subtraction statement, which cites this item and therefore cannot be used without creating a cycle.

## Review by Q57

I checked every new statement against its cited source. The projectivity node is exactly Tag 05FT and supplies projectivity of S over R under finite presentation, flatness and geometrically integral fibres. The residue criterion is exactly Tag 05FQ, with projective source, flat target and injectivity modulo the maximal ideal. The localization node is Tag 05CM(1), and the flat-cokernel node is Tag 058P. The item’s first step verifies that mS is prime because the fibre is a domain and then checks all hypotheses of 05FT; the finite direct sum S^r is projective and N_q is flat by assumption. The second step explicitly proves injectivity modulo m: an element killed after localization at q is killed at the generic prime by the assumed isomorphism, and the domain S/mS embeds in its fraction field. The third step identifies the map to N_q as the localization composite, spells out why injectivity of the composite implies injectivity of α after every tensor, applies 05CM to α_q, and then applies 058P to the universally exact cokernel sequence with flat middle term. Every citation quote is copied verbatim into `citations.json`, and the hypotheses used at each application are stated in the corresponding proof step. I tested edge cases r=0, N_q=0, and R a field: the arguments reduce respectively to the zero map, the zero cokernel case, and the ordinary generic-basis injection over a domain. No source error or duplicate was found.

5. Nothing remains unfinished.
