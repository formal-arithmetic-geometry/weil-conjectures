1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-proper-descends-field.json` — statement split, 4 proof steps.
- `dag/nodes/sec-picard-framework/lem-pc-field-extension-fpqc-cover.json` — statement-only node; Mathlib search verdict no match.
- `citations.json` — verbatim statement quotes for every cited node and step.

2. Attachments: none. No sorry-free slopmaster2 declaration states the item exactly; `AlgebraicGeometry.isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback` is still `sorry` and has a stronger, different statement.

3. WANTED: none. The Stacks Descent and Topologies tags used by the split are already identified in the imported node records; the local checkout does not contain the extracted `.tex` sources.

4. What was wrong or incomplete: the imported item had no proof and omitted the finite-type definition from `stmt_deps`. I added that dependency and supplied the four-step argument. The proof uses the existing generic fpqc descent lemmas for separatedness and universal closedness; these are declared as tool uses because they come from the proper-base-change unit.

## Review by G1

I checked the item against Stacks Descent Tag 02L1 as named by its source record and read the existing statements of `def-weil-proper-morphism`, `lem-weil-pbc-fpqc-descend-separated`, and `lem-weil-pbc-fpqc-descend-universally-closed`. Step 1 cites the new field-extension cover statement, the base-change definition, and the properness definition; those statements provide respectively the fpqc cover, the identification of the pullback with `X_K`, and the hypothesis that properness supplies separatedness and universal closedness. Steps 2 and 3 use exactly the conclusions of the two cited fpqc descent nodes, with the singleton cover and the properness clauses supplying their hypotheses. Step 4 uses the finite-type-over-a-field clause and the definition that proper means finite type plus separated plus universally closed.

For the new node, I checked the field-spectrum argument on the identity extension and on an arbitrary nontrivial extension: both spectra are one-point spaces, the map is surjective and quasi-compact, and the field inclusion is a free (hence flat) module map. I searched the DAG and blueprint for an existing singleton field-extension fpqc statement and found none. I recorded LeanSearch, Loogle, and Mathlib-source grep searches; the generic fpqc precoverage infrastructure was present but no packaged field-extension theorem. I also checked all citation quotes in `citations.json` against the node statements and verified the JSON files parse cleanly.

5. What could not be finished: no Lean compilation was performed, as required for stage 1.
