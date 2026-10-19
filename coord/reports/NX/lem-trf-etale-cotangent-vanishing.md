1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-etale-cotangent-vanishing.json`: statement split, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-etale-ring-map-weakly-etale.json`: statement-only helper, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-flat-epimorphism-derived-self-tensor.json`: statement-only helper, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-derived-diagonal-cotangent-vanishing.json`: statement-only helper, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-cotangent-bootstrap.json`: statement-only helper, no Mathlib match.
- `citations.json`: verbatim statement quotes for every item citation.

2. Attachments: none. No exact sorry-free project declaration exists for the item.

3. WANTED: none. The Stacks cotangent source is present locally at `literature/stacks-project/cotangent.tex`.

4. What was wrong or incomplete in the imported material: the item had no proof and its imported blueprint ancestry points to an unrelated local-term node, while its own source is the Stacks cotangent argument. I retained that ancestry and recorded the actual supporting ring/sheaf sentence in the split report. The statement itself agrees with the source intent and was not changed. The four helpers are genuine intermediate lemmas rather than restatements of the vanishing conclusion. No existing DAG node states the same Stacks Tag 08R0, 08R1, or 08R2 helper.

## Not duplicates

- `lem-trf-etale-ring-map-weakly-etale` vs `lem-trf-localization-cotangent-vanishing`: the helper proves weak-etale flatness from formal etale hypotheses; the existing node proves cotangent vanishing for a localization map.
- `lem-trf-flat-epimorphism-derived-self-tensor` vs `lem-trf-localization-cotangent-vanishing`: the helper is a general flat-surjection derived tensor calculation; the existing node concerns cotangent vanishing for localizations.
- `lem-trf-etale-ring-map-weakly-etale` vs `lem-trf-etale-cotangent-vanishing`: the helper concludes flatness of the ring and multiplication maps from the etale hypotheses; the item concludes vanishing of the full cotangent complex.
- `lem-trf-etale-ring-map-weakly-etale` vs `lem-weil-pbc-etale-algebra-finite-presentation-localization`: the helper treats arbitrary finitely presented formally etale maps and both flatness conclusions; the existing node concerns a localization presentation for a finite-presentation etale algebra.
- `lem-trf-etale-ring-map-weakly-etale` vs `lem-weil-pbc-etale-near-prime-naive-cotangent-vanishing`: the helper proves global weak-etale flatness; the existing node proves a local naive cotangent vanishing statement near a prime.
- `lem-trf-etale-ring-map-weakly-etale` vs `lem-weil-pbc-etale-ring-map-conormal-criterion`: the helper proves flatness from formal lifting; the existing node gives a conormal criterion for an already specified etale ring map.
- `lem-trf-etale-ring-map-weakly-etale` vs `lem-weil-pbc-etale-ring-map-iff-etale-affine`: the helper starts from square-zero lifting and concludes affine weak-etale flatness; the existing node compares the scheme etale property with finite presentation, H1, and Omega conditions.
- `lem-trf-etale-ring-map-weakly-etale` vs `lem-weil-pbc-finite-separable-extension-etale`: the helper applies to arbitrary formally etale maps; the existing node proves etaleness for a finite separable field extension.
- `lem-trf-etale-ring-map-weakly-etale` vs `lem-weil-pbc-finite-separable-multiplication-etale`: the helper proves weak-etale flatness; the existing node proves etaleness of a particular multiplication map for a finite separable extension.
- `lem-trf-etale-ring-map-weakly-etale` vs `lem-weil-pbc-smooth-zero-differentials-affine-open-etale`: the helper is a global ring-map criterion; the existing node constructs affine etale opens from smooth zero-dimensional fibres.
- `lem-trf-etale-ring-map-weakly-etale` vs `def-weil-weakly-etale-morphism`: the helper is a theorem deriving the two affine ring flatness conditions; the existing node is only the scheme-level definition.
- `lem-trf-etale-ring-map-weakly-etale` vs `lem-weil-iso-weakly-etale`: the helper starts from etale lifting data; the existing node proves weak-etaleness for an isomorphism.
- `lem-trf-flat-epimorphism-derived-self-tensor` vs `lem-trf-etale-cotangent-vanishing`: the helper is the derived tensor-square intermediate for a flat surjection; the item concludes cotangent-complex vanishing for etale maps.
- `lem-trf-etale-ring-map-weakly-etale` vs `det-pe-morphisms-etale-comparison`: the new node specializes the affine ring-map hypotheses to finite presentation plus square-zero lifting and records the two ring flatness conclusions; the existing node is a general scheme-level comparison with four clauses.
- `lem-trf-etale-ring-map-weakly-etale` vs `lem-weil-pbc-etale-algebra-flat`: the new node also proves flatness of the tensor-square multiplication map from the explicit ring hypotheses; the existing Mathlib leaf proves only target flatness after assuming an etale affine scheme morphism.
- `lem-trf-etale-ring-map-weakly-etale` vs `lem-weil-pbc-weak-etale-tor`: the new node establishes weak-etale flatness from etale hypotheses; the existing node compares Tor groups after weak-etale flatness is already assumed.
- `lem-trf-flat-epimorphism-derived-self-tensor` vs `lem-trf-derived-diagonal-cotangent-vanishing`: the former identifies a derived tensor square from flatness and an underived multiplication isomorphism; the latter deduces cotangent vanishing from that derived-square isomorphism.
- `lem-trf-cotangent-bootstrap` vs `lem-trf-cotangent-transitivity-triangle`: the former is the Tor-vanishing consequence of the transitivity argument; the existing node only states the canonical distinguished triangle.

5. What I could not finish: the four helper nodes are intentionally statement-only stage-1 deliverables and remain unsplit for later workers. The item split, citations, searches, and review are complete.

## Review by NX

I read the imported item, its source entry, the blueprint ancestry, the Stacks cotangent text at Tags 08R0, 08R1, and 08R2, and the statements of every node cited by the item. The item statement has the finite-presentation and square-zero lifting hypotheses exactly as imported, and its conclusion uses the standard cotangent complex and derived category dependencies already named there.

Step 1 cites `lem-trf-etale-ring-map-weakly-etale`, whose statement explicitly takes those two hypotheses and supplies both facts used later: flatness of (C) over (R) and flatness of (C\otimes_R C\to C). I checked that this is the affine form of the weakly etale reduction in Tag 08R2 case (5) to case (1), and recorded the distinctions from the existing scheme comparison and Tor nodes above.

Step 2 cites `lem-trf-flat-epimorphism-derived-self-tensor` for the multiplication map's flatness and its surjectivity-induced derived tensor isomorphism, then cites `lem-trf-derived-diagonal-cotangent-vanishing` for the exact hypothesis and conclusion of Tag 08R0. Substituting (A=C\otimes_R C) and (B=C) makes the displayed derived tensor square precisely the one required by the diagonal lemma, and yields (L_{C/(C\otimes_R C)}=0).

Step 3 uses `lem-trf-cotangent-bootstrap`, whose statement requires exactly the two facts established in the previous steps: positive Tor vanishing and zero relative cotangent complex. Flatness of (C) over (R) supplies the Tor vanishing, and the prior diagonal calculation supplies the relative cotangent hypothesis. This is Tag 08R1, after which the derived-category cohomology formulation is definitional.

For each new node I read its Stacks source place, searched the whole DAG and blueprint for its tag and key terms, and ran the recorded LeanFinder, Loogle, and Mathlib-grep searches. The searches found only partial Mathlib facts (flatness, formal etaleness, or generic cotangent constructions), so no helper was marked as a Mathlib leaf. I also checked small edge cases conceptually: for an identity or localization map the multiplication map is an isomorphism and all four helper conclusions specialize correctly; no Noetherian or characteristic hypothesis was introduced.
