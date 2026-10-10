1. Files written

- `dag/nodes/sec-picard-framework/lem-sc-ext-derived-composite-natural.json`: statement node, split into three proof steps; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-acyclic-comparison-natural.json`: statement-only auxiliary node; no Mathlib match.
- `citations.json`: verbatim statement excerpts for every cited node at every step.

2. Attachments

None. No sorry-free slopmaster2 declaration states either node exactly.

3. WANTED:

None. The cited Stacks source is present locally.

4. Problems found

The item was already present but unsplit and its only Mathlib search was a source grep. The proof needs the naturality of the acyclic-resolution comparison, which was not stated by the existing Leray criterion node, so I created `lem-sc-acyclic-comparison-natural` as a strictly more general statement-only node. The item uses the existing generic right-derived-functor map formula as a tool; it is outside the Picard-duality unit because no unit node states that formula.

5. Unfinished work

No unfinished work. The new auxiliary statement is intentionally unsplit and joins the stage-1 queue.

## Review by G1

I read the item node, the `sk-thm-picard-duality` unit, the `sec-picard-framework` chapter record, and the Stacks `derived.tex` material for Lemmas 015M and 015E. I also opened the existing statements of `lem-sc-ext-derived-composite`, `lemma-weil-pbc-leray-acyclicity`, `lem-weil-pbc-derived-functor-map-via-lift`, `def-sp-injective-resolutions`, and `def-sp-acyclic`. The item keeps its hypotheses: both source categories have enough injectives, both exact functors send injectives to U-acyclic objects, and the conclusion is degreewise naturality of the canonical comparison.

Step 1 uses only the injective-resolution definition and the acyclicity definition, together with exactness and the stated hypotheses. The cited definitions say respectively that the chosen complex is bounded below and exact in the required sense, and that the terms are U-acyclic. I checked the edge cases T = 0, T' = 0, and i = 0; the construction reduces to the evident maps.

Step 2 uses the new auxiliary statement exactly in its displayed square, with F = T(M), F' = T'(M), h = alpha_M, and phi = alpha on the chosen resolution. Its statement explicitly gives the comparison square, while `lem-sc-ext-derived-composite` states that these are the canonical derived-composite isomorphisms. No proof detail from either node is used beyond its statement.

Step 3 uses the existing Mathlib leaf `lem-weil-pbc-derived-functor-map-via-lift`; its statement explicitly identifies R^n v(h) with the cohomology map of a lift between injective resolutions. The auxiliary node supplies the compatibility with the acyclic comparison. I checked the degree-zero case and the identity natural transformation, where both sides are identities.

For the new node I searched the whole DAG and blueprint for acyclic-resolution comparison naturality and for Tag 015E before writing it. I recorded LeanSearch, Loogle, LeanFinder, and Mathlib-source grep results; the only Mathlib matches are the narrower injective-resolution declarations `Functor.rightDerived_map_eq` and `InjectiveResolution.rightDerived_app_eq`. The new node is statement-only as required, introduces all categories, functors, resolutions, morphisms, and comparison maps, and records its Stacks Tag 015E source and blueprint ancestor. `citations.json` quotes the exact statements used by each proof step.
