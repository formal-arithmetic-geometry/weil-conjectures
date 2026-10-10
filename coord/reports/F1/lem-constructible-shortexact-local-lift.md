1. Files written:
   - `dag/nodes/sec-proper-base-change/lem-constructible-shortexact-local-lift.json`: completed the two-step proof and added the exact-sequence statement dependency.
   - `citations.json`: added verbatim citations for both proof steps.

2. Attachments:
   - None.

3. WANTED:
   - None.

4. What was wrong or incomplete:
   - The imported item had no proof, no proof dependencies, and omitted the exact-sequence definition from `stmt_deps` even though the proof needs the implication that the quotient map is epi.
   - No new supporting node was needed: the existing `lem-weil-pbc-abelian-sheaf-epi-locally-surjective` states exactly the local lifting conclusion for an epimorphism of etale abelian sheaves.

5. What I could not finish:
   - Nothing.

## Review by F1

I read the item source, the blueprint extension paragraph in `lemma-constructible-flc-serre.md`, the item node, and the two cited DAG statements. The item statement is unchanged and its hypotheses are explicit: a scheme, coefficient ring, small etale site, sheaves of modules, and a short exact sequence. I checked that `def-weil-pbc-exact-sequence` defines a short exact sequence equivalently by requiring the right-hand map to be an epimorphism, so step 1 uses the cited statement exactly. I then checked that `lem-weil-pbc-abelian-sheaf-epi-locally-surjective` states the needed covering and lifted-section conclusion for every etale object and section, matching step 2 after substituting `\\mathcal E`, `\\mathcal N`, and `\\pi`. Step 1 is elementary once the exact-sequence definition is cited; step 2 is the non-elementary theorem application. I searched the DAG, blueprint, Lean source, and Mathlib searches recorded on the existing generic node before deciding not to create a duplicate. I also tested the boundary cases conceptually: for the identity quotient map the cover can be the identity, and for the zero section any local lift of zero supplied by the epimorphism criterion is valid; no splitting of the short exact sequence is assumed.
