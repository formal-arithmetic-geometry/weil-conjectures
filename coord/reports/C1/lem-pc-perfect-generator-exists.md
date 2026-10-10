1. Files written

- `dag/nodes/sec-picard-framework/lem-pc-perfect-generator-exists.json`: item split; no new nodes.
- `citations.json`: verbatim statement quotes for all cited nodes and steps.

2. Attachments

None.

3. WANTED

None.

4. Problems found

The item was unsplit although its proof inputs had already been split into existing DAG nodes. No statement was changed. The imported `blueprint.from.place` was already the correct Tag 0AA8 perfect-generator sentence; the proof now realizes it through the Tag 09IS route. The source literature checkout available on this machine is the Stacks review copy; the item source and the existing neighbour nodes identify Tag 09IS and Tag 09SN precisely.

5. Unfinished work

None.

## Second reading by C1

- Item statement: checked against Stacks Tag 09IS and Tag 09SN; hypotheses and the localizing/retract-closed conclusion agree.
- Step 1: checked against `lem-pc-perfect-generation-affine-base`; its affine hypothesis and shifted-Hom criterion are exactly used.
- Step 2: checked against `lem-pc-perfect-generation-open-induction-step`; qcqs X, quasi-compact U, affine V, and the perfect-generator conclusion are all in force.
- Step 3: checked against `lem-sc-invert-s-cohomology-induction`; the property matches its affine-base and U/V/intersection-to-union induction premise.
- Step 4: checked against `lem-pc-derived-qcoh-direct-sums`, `lem-pc-perfect-object-compact`, `def-pc-generators`, and `lem-pc-compact-generators-build-objects`; these supply coproducts, compactness, generation, and the telescope construction.
- New nodes: none; B1-B7 and duplicate/new-node checks are vacuous.
- Small cases: affine schemes reduce to the structure-sheaf criterion; the zero object satisfies the criterion; the empty scheme has the zero derived category and zero generator; no n-parameter occurs.
- Changes: added this second-reading audit; no mathematical or node statement changes were required.

## Review by C1

I read the item source reference (Stacks Tag 09IS, perfect-generator remark) and the existing proof packet `lem-pc-derived-qcoh-perfect-generation.json`, including its four-step proof and review note. Step 1 cites `lem-pc-perfect-generation-affine-base`; its statement explicitly supplies that the structure sheaf on an affine scheme is perfect and detects zero by all shifted Hom groups. Step 2 cites `lem-pc-perfect-generation-open-induction-step`; its statement explicitly supplies the perfect objects Q and K' and says their direct sum is a generator on the union. Step 3 cites `lem-sc-invert-s-cohomology-induction`; I checked its hypotheses and conclusion, including quasi-compactness, quasi-separatedness, affine base cases, and the U-union-V implication, against the property used in the step. Step 4 cites `lem-pc-derived-qcoh-direct-sums`, `lem-pc-perfect-object-compact`, `def-pc-generators`, and `lem-pc-compact-generators-build-objects`; I read each statement. Together they provide set-indexed sums, compactness of G, the coproduct-generator meaning, and the telescope construction from coproducts of shifts and cones. The resulting closure argument is the stated localizing, retract-closed generation claim. Every citation quote in `citations.json` is copied verbatim from the cited node statement. I also checked that no cited node depends on this item, so the split is acyclic, and that no new node is a restatement or elementary fragment of the item.
