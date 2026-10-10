1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-ext-sheaf-to-global-spectral-sequence.json` — statement split into three proof steps.
- `dag/nodes/sec-picard-framework/lem-sc-ext-coherent-hom-injective-acyclic.json` — statement-only supporting node; no Mathlib match.
- `citations.json` — verbatim step citations.

2. Attachments: none.

3. WANTED: none.

4. The item was unsplit and had no matching declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; the item id and its key terms also had no source declaration. I read the item, `thm-sc-p1-duality` as its blueprint ancestor, the unit and chapter records, and the existing statements of `thm-sp-grothendieck`, `def-sp-left-exact-additive`, `lem-weil-pbc-scheme-modules-enough-injectives`, `def-weil-pbc-sheaf-ext`, `pqf-def-cohomology`, and `lem-weil-pbc-ext-via-injective-resolution`. Step 1 uses the generic Grothendieck spectral sequence, the module-category enough-injectives statement, left exactness, and the new coherent-Hom acyclicity statement; each cited statement supplies exactly the corresponding hypothesis. Step 2 substitutes the sheaf Ext, sheaf cohomology, and injective-resolution descriptions into the generic page and abutment. Step 3 uses the finite filtration supplied by first-quadrant convergence to derive the total-degree vanishing. I searched the DAG and blueprint for each supporting fact before adding the new node, and recorded LeanSearch, Loogle, and Mathlib-source searches for it.

## Source error

The existing `def-sc-ext-sheaf` node defines Ext using the contravariant functor `Hom(-, G)`, which is not the injective-resolution convention used by the local-to-global theorem and is flagged by that node's own lead note. The proof step therefore records the corrected injective-resolution interpretation through `lem-weil-pbc-ext-via-injective-resolution`; I did not change the imported statement.

5. I could not run the delivery preflight from the repository because this worker is restricted to the sandbox and the delivery command operates on the remote-group checkout. The sandbox JSON parses successfully, and every citation quote was copied from the cited node statement.

## Review by E1

I checked the item source and blueprint ancestor, then read every cited node's statement rather than relying on its proof text. The Grothendieck node explicitly gives a first-quadrant sequence with the displayed derived-functor page and abutment; the new node states the required global-sections acyclicity for `Hom(F, I)`; the module-category node supplies enough injectives; and the left-exactness definition supplies the functor hypotheses. The sheaf-Ext definition states that its terms are cohomology sheaves of derived internal Hom, the cohomology definition identifies the right derived global-sections functors, and the injective-resolution node identifies the corrected global Ext with the derived composite. I verified the hypotheses are attached to the correct categories and that the final filtration argument only uses first-quadrant convergence. I corrected the item dependency list to include the existing sheaf-Ext definition, added the missing acyclicity node after searching the DAG and blueprint, and recorded the pre-existing Ext-definition source error explicitly.
