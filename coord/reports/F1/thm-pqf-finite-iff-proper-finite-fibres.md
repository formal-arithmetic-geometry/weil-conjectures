# Stage-1 report: thm-pqf-finite-iff-proper-finite-fibres

1. Files written:

   - `dag/nodes/sec-abelian-varieties/thm-pqf-finite-iff-proper-finite-fibres.json` — statement, split; no new nodes.
   - `citations.json` — verbatim quotes for all cited statements in both proof steps.

2. Attachments: none.

3. WANTED: none.

4. What was wrong in the imported node: its reverse implication expanded into an unverified formal-functions and Serre-criterion route, although the unit route is the proper-and-quasi-finite theorem. I replaced it with the shorter valid route already supported by the DAG and Mathlib. The locally Noetherian assumption remains in the theorem statement as required by Tag 02OG, although the revised reverse implication does not use it.

## Review by F1

I read the imported node, the unit record `sk-prop-av-pqf-finite`, the chapter record, and the statements of every cited dependency. For step 1, `lem-weil-pbc-finite-proper` supplies properness of a finite morphism, `pqf-lem-finite-qf` supplies quasi-finiteness, and `pqf-lem-qf-finitefibres` explicitly supplies finite fibres from quasi-finiteness. For step 2, `pqf-lem-proper-basic` supplies finite type, locally finite type, and quasi-compactness; the converse clause of `pqf-lem-qf-finitefibres` therefore supplies quasi-finiteness from the assumed finite fibres. The statement of `pqf-lem-qf-locqf-qc` then supplies local quasi-finiteness. I checked Mathlib source `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`, lines 373–381, and `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean` for the final proper-plus-locally-quasi-finite implication.

I searched the DAG for the Stacks tag and key phrases before adding anything; the existing corollary is downstream and depends on this item, so it cannot be cited without a cycle. The four required Mathlib searches were run for the item; LeanSearch was unavailable and is recorded as such. No new statement needed small-case testing because no new node was created. The imported proof's formal-functions dependencies were removed because they were not needed by the corrected unit route.

## Second reading by F1

- Item statement: checked against Stacks Tag 02OG (Lemma 30.21.1) and the imported blueprint statement; the hypotheses are exactly a morphism of schemes and locally Noetherian target, with equivalence between finite and proper with finite fibres.
- Step 1: checked against `lem-weil-pbc-finite-proper`, `pqf-lem-finite-qf`, and `pqf-lem-qf-finitefibres`; each cited statement supplies the corresponding properness, quasi-finiteness, and finite-fibre implication, and no uncited geometric fact is used.
- Step 2: checked against `pqf-lem-proper-basic`, `pqf-lem-qf-finitefibres`, and `pqf-lem-qf-locqf-qc`; the properness consequences give finite type, locally finite type, and quasi-compactness, finite fibres give quasi-finiteness, and the cited equivalence gives local quasi-finiteness. The final proper-plus-locally-quasi-finite implication is the Mathlib declaration `AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite` / `AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`, inspected in `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean` and `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean` (lines 373–381).
- New nodes: none; therefore B1–B7 and new-node small-case checks are vacuous. I searched `dag/nodes` for the item tag and dependency names before retaining the split; the downstream corollary was not usable because it would create a cycle.
- Edge cases: finite maps over a field and over the empty scheme satisfy both directions; the zero/empty fibre case is covered by the finite-fibre definition; no step requires a positive dimension or a nonzero integer parameter.
- Searches: reran the required semantic, Loogle, and Mathlib-source searches; LeanSearch was unavailable and is recorded as unavailable in `searches.jsonl`.

Changes made in this second reading:

- Filled the item's blueprint `from.node` and exact proof `from.place`, and normalized `same_as` to an empty list.
- Added this review section with per-step citation checks, source and edge-case checks, and the reason the imported formal-functions route was replaced by the shorter unit route.
