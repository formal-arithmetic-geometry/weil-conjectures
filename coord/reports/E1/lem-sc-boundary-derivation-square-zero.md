1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-boundary-derivation-square-zero.json` (repaired item; four proof steps, no Mathlib match).
- `dag/nodes/sec-curve-estimates/lem-sc-boundary-cech-local-lifts.json` (new unsplit statement node, no Mathlib match).
- `citations.json` (verbatim statement quotes for every cited node and step).

2. Attachments: none.

3. WANTED: none. The source is present at `/home/ubuntu/c1-stacks-review/cohomology.tex` and was read for Lemmas 0B8R and 0B8S.

4. What was wrong and what changed: the returned delivery moved the whole 0B8S theorem into `lem-sc-boundary-derivation-ringed-space` and used step 2 only as a relabelling. I deleted that node. The item now follows the source proof itself: (1) square-zero factorization gives the O-module structure and the long exact sequence; (2) the connecting map is additive; (3) local lifts produce the Cech cocycles representing the boundary classes, using a new node stating 0B8R plus the boundary description; (4) the displayed overlap identity gives the Leibniz rule. The new node has the required `created` record and complete blueprint reference. The stale WANTED line was removed.

## Review by E1

I read `/home/ubuntu/c1-stacks-review/cohomology.tex`, specifically Lemma 0B8R (`lemma-cech-h1`) at the Cech-to-cohomology section and Lemma 0B8S (`lemma-boundary-derivation-over-cup-product`) at the boundary derivation proof. The item statement remains the square-zero specialization used in the 09MS proof, with the same surjection, kernel, connecting map, module action, and Leibniz conclusion. The new node states exactly the 0B8R injectivity assertion together with the 0B8S local-lift description of the boundary, and introduces its scheme, sequence, cover, lifts, cocycle, and connecting class explicitly.

Step 1 cites `pqf-def-cohomology` for the derived-functor cohomology sequence; the factorization through O is the one-line I^2=0 calculation from the source. Step 2 cites the same long-exact-sequence statement for the additive connecting homomorphism and follows the source sentence that additivity reduces the proof to Leibniz. Step 3 cites `lem-sc-boundary-cech-local-lifts`, whose statement says both that the Cech-to-H^1 map is injective and that the local-lift cocycle represents the connecting class; its final sentence covers the simultaneous choice of the g_i and the product lifts. Step 4 uses that same statement for the three boundary classes and writes the source's displayed overlap identity explicitly; the replacement of g_i and f_i by their images g and f in the I-module is justified by I^2=0.

I searched the DAG and blueprint for an existing 0B8R/local-lift boundary node and found none. I searched Mathlib for the new Cech boundary statement with LeanSearch, LeanFinder, and source grep; all reported no match, so it is statement-only. I checked the split dual-number extension (all boundaries zero) and the zero-kernel case as small cases. The former ringed-space node was removed, the proof dependencies and citations were updated, and JSON parsing succeeds for both nodes and `citations.json`.
