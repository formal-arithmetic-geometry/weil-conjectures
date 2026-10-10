1. Files written:

   - `dag/nodes/sec-picard-framework/lem-sc-local-splitting-finite-free.json`: item split into three proof steps.
   - `dag/nodes/sec-picard-framework/lem-sc-local-section-quotient-finite-free.json`: one new unsplit statement-only node; Mathlib search found no sheaf-level match.
   - `citations.json`: verbatim citations for each cited step.

2. Attachments: none.

3. WANTED: none.

4. What was wrong or incomplete: the imported item had no proof and its `created` metadata belonged to the determinant item. I corrected the metadata, filled the blueprint location, and supplied the local-section dependency and direct inverse-map argument. The Lean source was searched for the item tag and for local-splitting declarations; no sorry-free or sorry-bearing declaration states this item.

5. What I could not finish: the new local-section statement remains unsplit as required for a new non-Mathlib node.

## Review by M1

I read the determinant paragraph in the imported Riemann--Roch blueprint text embedded in `lem-sc-riemann-roch.json`; it says to split the sequence locally by lifting a basis of the locally free quotient. I also read `def-amb-finite-locally-free-module.json`, whose statement supplies the open trivializations used by that argument, and searched all DAG nodes and the Mathlib source for an existing sheaf local-splitting theorem. The new node states exactly the local right inverse needed by step 1, introduces the scheme, exact sequence, quotient, and rank hypotheses itself, and is statement-only.

Step 1 cites the new node's verbatim assertion that every point has an open neighbourhood and a section with `q ∘ s = id`; no other non-elementary fact is used. Step 2 uses the same exact-sequence hypotheses and section statement, then defines `Phi` and `Psi` and checks both composites by substitution; this is elementary module algebra once the cited section exists. Step 3 only observes that the chosen neighbourhoods cover `X`, so it is elementary. I tested the construction in ranks `(0,0)`, `(1,0)`, `(0,1)`, and `(1,1)`; the formulas reduce respectively to the identity, the evident inclusion/projection, and the usual two-component decomposition. I verified all new-node identifiers are unique, all citations quote literal text from the cited node, and the item proof dependencies equal the union of its step uses.
