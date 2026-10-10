1. files written

- `dag/nodes/sec-curve-estimates/lem-sc-affine-standard-cover-finite-projective.json`: split item.
- `dag/nodes/sec-curve-estimates/lem-sc-affine-standard-cover-finite-presentation-flat.json`: new statement-only node; no Mathlib exact match.
- `citations.json` and this report.

2. attachments

None. A search of `WeilConjectures/` for the item id and the relevant theorem names found no sorry-free declaration stating this item exactly.

3. WANTED:

None. The cited Stacks source is already named in the node; the checkout does not contain the imported Stacks TeX tree, so the proof route is recorded from the tag and existing DAG source references.

4. what was wrong or incomplete

The imported item had no proof or proof dependencies despite being the reverse direction of Stacks Tag 00NX. The DAG already contains the opposite implication (`lem-weil-pbc-finite-projective-standard-free-cover`) and the Mathlib-backed criterion `lem-weil-pbc-finitely-presented-flat-module-projective`; I searched the whole DAG before adding the new cover criterion and found no node stating the needed reverse implication. The item now has two steps: the standard-open cover gives finite presentation and flatness, then the existing criterion gives projectivity. The new node is intentionally statement-only as required for an unsplit non-Mathlib fact.

5. what I checked

I read the item, its unit and chapter records, the source-side declaration search in `WeilConjectures/AlgebraicGeometry/Modules/LocallyFreeAffine.lean`, and the existing cited DAG nodes. The source declaration `finitePresentation_projective_sections` confirms the same finite-standard-open localization mechanism in the project. For step 1, the new node states exactly the finite presentation and flatness conclusion used; its hypotheses reproduce the item, including the unit-ideal cover and finite freeness. For step 2, the cited node states that a finitely presented flat module is projective and hence finite projective, and the projective-module definition is cited for the final terminology. I checked small cases conceptually: the empty module and a rank-one free module over a one-element cover satisfy the criterion, and localization at a unit reduces to the original module. Mathlib searches for the new node used LeanSearch, LeanFinder, and source grep; only component lemmas (`Module.Finite.of_localizationSpan_finite`, `IsLocalization.flat`) were found, not the combined converse.

## Review by C1

I checked the item against Algebra Tag 00NX, implication (7) => (1) => (2) => (3), and verified that its assumptions and conclusion match the source direction. I opened the existing node `lem-weil-pbc-finitely-presented-flat-module-projective`; its statement explicitly supplies projectivity from finite presentation plus flatness, so it supports step 2. I also opened `def-weil-pbc-projective-module` to verify the final term is the intended projective-module notion. Step 1 cites the new node whose statement repeats exactly the cover hypotheses and gives the two properties it uses; no hidden theorem is being attributed to the node's proof. The new node was searched against all DAG nodes and the project source before creation, and its Mathlib searches record all three required search kinds with no exact combined declaration. The item statement was tested on the zero module and a rank-one module with a unit generator; no hypothesis was added or dropped. The only correction to the imported item was to replace the empty proof with these explicit dependencies and to fill the blueprint and split report.
