1. Files written:

   - `dag/nodes/sec-picard-framework/lem-sc-local-section-quotient-finite-free.json`: item split into three proof steps; no new node was needed.
   - `citations.json`: verbatim citations for each cited step.

2. Attachments: none.

3. WANTED: none.

4. What was wrong or incomplete: the imported item was statement-only. I supplied the missing local proof and added the exact module-local-lifting dependency already present in the DAG. The item remains in the Riemann--Roch determinant route and its statement is unchanged in substance, with the exact-sequence and module-category notions made explicit in `stmt_deps`.

5. What I could not finish: none.

## Review by M1

I read the item source recorded in `lem-sc-riemann-roch.json`, specifically the determinant paragraph of the proof of (*), whose local-splitting sentence is realized here. I also read the full statements of `def-amb-finite-locally-free-module`, `def-weil-pbc-exact-sequence`, `def-weil-sheaf-of-modules-category`, and `lem-weil-pbc-ringed-space-module-exactness-local-lifting`; the citations file quotes the exact parts used.

Step 1 uses the local-free definition to choose a Zariski trivialization and a finite basis. Step 2 uses the short-exact definition's assertion that the quotient map is an epimorphism, then the existing ringed-space lemma's local-lifting clause to lift each basis section; finiteness permits a common neighbourhood. Step 3 uses the basis description and the module-morphism definition to define the section and checks the right-inverse identity coefficientwise. I checked the rank-zero edge case separately: the quotient is the zero module and the unique map is a right inverse. I searched the whole DAG and blueprint for a duplicate local-section theorem and found none; the Mathlib searches recorded in the item found only module-level results, not a sheaf theorem. The only route tool is the existing generic ringed-space lifting lemma, declared in `split_report.tool_uses` because the Picard Riemann--Roch unit does not provide that generic fact.
