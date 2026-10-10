1. Files written:
   - `dag/nodes/sec-picard-framework/lem-pc-smooth-characterization.json`: split into one specialization step; no new nodes.
   - `citations.json`: verbatim citation for the existing criterion node.
2. Attachments: none.
3. WANTED: none.
4. The imported proof expanded the Stacks criterion into a local standard-smooth/Jacobian argument, but the DAG already contains the stronger general criterion `sbc-lem-smooth-criterion`. I replaced those paragraphs with the valid specialization under the item's local finite presentation hypothesis.
## Review by C1

I read the item source blueprint and the complete statement of `sbc-lem-smooth-criterion`. That node explicitly says smoothness is equivalent to flatness, local finite presentation, and smoothness of every fibre over the residue field, exactly the fact used by the sole proof step. The item's local finite presentation hypothesis makes the middle conjunct redundant, so the specialization is elementary. I checked slopmaster2's `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/SmoothFiber.lean`: its theorem includes local finite presentation on the right and therefore is not an exact attachment to this externally assumed-hypothesis statement. The recorded LeanFinder, Loogle, and grep searches were run; LeanSearch was unavailable and is not recorded. Identity morphisms and affine-space projections give basic sanity checks.

## Second reading by C1

- Item statement: checked against Stacks Tag 01V8 (Lemma 29.35.3) and Tags 00TF, 00T7, and 00T4; hypotheses and conclusion agree.
- Step 1: checked against `sbc-lem-smooth-criterion`; it supplies the full criterion, and removing the assumed presentation conjunct is elementary.
- New nodes: none; no new node requires statement, source, Mathlib, or small-case review.
- Edge cases: identity morphisms and affine-space projections satisfy both sides; empty fibres make the universal fibre clause vacuous consistently with the criterion.
- Changed the sandbox statement encoding to use actual JSON newlines instead of literal `\\n` text.
