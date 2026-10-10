1. Files written:

- \`dag/nodes/sec-picard-framework/lem-sc-smooth-proper-relative-dualizing-general.json\`: repaired split of the item.
- \`lem-sc-smooth-proper-diagonal-koszul-regular\`: statement-only, no Mathlib match.
- \`lem-sc-smooth-proper-diagonal-pushforward-structure\`: statement-only, no Mathlib match.
- \`lem-sc-smooth-proper-diagonal-tensor-formula\`: statement-only, no Mathlib match.
- \`lem-sc-smooth-proper-diagonal-koszul-dual\`: statement-only, no Mathlib match.
- \`lem-sc-smooth-proper-diagonal-conormal-differentials\`: statement-only, no Mathlib match.

2. Attachments: none.

3. WANTED: none.

4. The returned nonproper upper-shriek node was false and has been deleted. The item now follows the proper proof route through Tags 0BRT, 0A9E, 08DW, 067U, 068C, 0E2Q, 0A9U, 0BR0, and 08S2. The diagonal node now states the closed-diagonal condition directly and defines Koszul regularity and perfect immersion; the tensor node defines perfectness via local perfectness of the pushforward; the Koszul-dual node distinguishes the conormal C_i from the normal N_i=SheafHom(C_i,O_Z). Step 7 now writes the full cancellation chain and obtains the inverse determinant line before identifying it with the top exterior power of the conormal sheaf.

5. Nothing remains unfinished in this repair.

## Review by H1

I read the returned item, the blueprint ancestor \`lem-sc-finite-duality\`, the existing Noetherian right-adjoint node, and the Stacks route named in Tags 0BRT, 0A9E, 08DW, 067U, 068C, 0E2Q, 0A9U, 0BR0, and 08S2. Step 1 uses the existing right-adjoint statement. Step 2 uses the diagonal node's closed-diagonal hypothesis, Koszul-regular conclusion, codimension, perfectness, and properness. Steps 3–6 use the corresponding flat/proper, closed proper perfect immersion, Koszul-regular closed immersion, and C_Delta conormal statements; I checked each cited statement says the fact used. Step 7 explicitly applies the tensor and dual formulas, cancels the invertible top exterior power of the normal sheaf, takes its inverse, and identifies it with the top exterior power of C_Delta. I checked d=0 and d=1 as edge cases. Every new node remains statement-only, has blueprint provenance, and records LeanSearch, Loogle, and source-grep searches. This repair addresses the returned normal/conormal error, missing inline definitions, missing separatedness definition, and inverse cancellation error; every entry in \`citations.json\` is a verbatim substring of its cited statement.

