# Stage-1 Worker Report

1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-ext-support-cohomology-vanishing.json` — statement node, split; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-support-dimension-cohomology-vanishing.json` — statement-only node, no Mathlib match.

2. Attachments: none. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `/home/ubuntu/weil-conjectures-slopmaster2/WeilConjectures` carries either statement.

3. WANTED: none.

4. The imported item had no proof. I retained its statement and source, filled the blueprint location, and split the proof into the stalk calculation, the support-dimension estimate, the closed-support cohomology vanishing, and the case `q>d`. The new support-dimension cohomology node is statement-only because it is the non-elementary Stacks 02UZ plus closed-immersion reduction used by the item; Mathlib searches found no matching theorem. Existing nodes were reused for stalk localization, regular-local Ext vanishing, the generalization-chain dimension description, coherent support closedness, and topological cohomology vanishing.

5. What I could not finish: no Lean code was written, as required for stage 1. The delivery preflight is the remaining mechanical check.

## Review by E1

I read the item, its unit `sk-thm-picard-duality`, chapter `sec-picard-framework`, and the neighboring reviewed Ext nodes. I checked the source proof in `literature/stacks-project/equiv.tex` at Tag 0FZ3 and the cohomology source at Tag 02UZ. Step 1 uses the existing stalk-localization statement and the regular-local Ext vanishing statement exactly as written, including the finitely generated first module hypothesis supplied by coherence. Step 2 uses the same local statements, the existing generalization-chain characterization of local-ring dimension, and the definition of scheme dimension; concatenating chains gives the claimed bound on each irreducible support component. Step 3 checks that coherent sheaf Ext has closed support via the existing finite-type support node, then applies the new statement-only support-cohomology node with `r=d-q`. Step 4 handles `q>d` separately using the supremum definition of `d`, so the support is empty before invoking cohomology. I searched the DAG and blueprint for duplicate support-dimension or Ext-cohomology statements, searched the Lean source for an exact declaration, and recorded LeanSearch, LeanFinder, and Mathlib-source searches for the new node. I also checked the edge cases `q>d`, `q=d`, empty support, and a zero-dimensional regular scheme.
