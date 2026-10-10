1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-projection-formula.json`: item split; no Mathlib leaf.
- `dag/nodes/sec-picard-framework/lem-pc-projection-locality.json`: statement-only; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-affine-qcoh-derived-equivalence.json`: statement-only; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-derived-module-free-generation.json`: statement-only; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-derived-direct-image-direct-sums.json`: statement-only; no Mathlib match.

2. Attachments: none.

3. WANTED: none; the Stacks sources cited by the imported item are present in the project literature index.

4. The imported proof was one paragraph with no dependencies despite using locality, the affine derived equivalence, generation of D(A), and preservation of direct sums. I separated these into four statement-only nodes and rewrote the item into three proof steps. The Lean declaration carrying the blueprint tag is still `sorry` and only states the invertible-module higher-direct-image specialization, so it is not an attachment.

## Not duplicates

`lem-pc-derived-module-free-generation` vs `lem-pc-derived-qcoh-compact-generation`: the new node is the explicit affine D(A) generation by shifts of the ring; the existing node only asserts compact generation of D_QCoh(O_X) for qcqs schemes.

`lem-pc-derived-direct-image-direct-sums` vs `lem-pc-derived-qcoh-direct-sums`: the new node concerns preservation of sums by a derived direct-image functor; the existing node only asserts that D_QCoh itself has sums.

`lem-pc-affine-qcoh-derived-equivalence` vs `lem-pc-projection-formula`: the new node states the affine derived-global-sections equivalence used as an input; the existing item states the projection-formula isomorphism and only cites Tag 08CU as its source.

`lem-pc-derived-module-free-generation` vs `lem-pc-projection-formula`: the new node states the generation theorem for D(A) used in the proof; the existing item is the projection-formula statement whose proof invokes that theorem.

`lem-pc-derived-direct-image-direct-sums` vs `lem-pc-projection-formula`: the new node states preservation of direct sums by Rf_* as an independent input; the existing item states the projection-formula isomorphism and only cites Tag 08EU in its proof source.

`lem-pc-projection-locality` vs `lem-pc-projection-formula`: the new node states only the locality criterion for an already-defined canonical map on an open cover; the item asserts that map is an isomorphism globally.

## Review by C1

I read the target source entry and the tagged Lean docstring in `AlgebraicGeometry/Cohomology/DirectImage.lean` (lines 443–458). The Lean theorem has a `sorry`, and its hypotheses and conclusion are the higher-direct-image/invertible-module case, so I retained the full derived statement from the DAG rather than attaching the theorem. I checked the Stacks references 08CU and 08EU listed for the item and used them as the sources for the affine equivalence, free-generation, and direct-sum preservation nodes; the locality step follows the canonical-map locality described around Equation 20.54.2.1.

For item step 1, the cited locality node states exactly that the projection map is an isomorphism iff all restrictions over an open cover are. For step 2, the affine-equivalence node states the D_QCoh(O_Y) to D(A) identification used, the direct-sums node states the preservation property used for closure under sums, and the free-generation node states that shifts A[k] generate under the closure operations. I verified the hypotheses (f qcqs, Y affine in step 2) match those statements. Step 3 is the direct specialization to an invertible locally free module and is elementary. I also ran LeanFinder, Loogle, and Mathlib grep searches for each new statement; they found only general derived-category or sheaf declarations, with no matching theorem.
## Second reading by C1

- Item statement: checked against Stacks Lemma 36.22.1, Tag 08EU; the derived projection formula and qcqs hypotheses agree, and the imported 08CU citation was removed because 08CU is only the chapter tag.
- Step 1: checked against Equation 20.54.2.1 and the locality reduction in Tag 08EU; the locality node supplies the complete cited statement.
- Step 2: checked against Lemma 36.3.5 (Tag 06Z0), Lemma 36.4.5 (Tag 08DZ), and Remark 15.60.11 (Tag 09PB); each cited node supplies the affine equivalence, direct-sum preservation, and generation closure used.
- Step 3: checked on the zero complex and an invertible module in degree zero; local freeness makes the derived and ordinary tensor expressions coincide, so the specialization is elementary.
- `lem-pc-projection-locality`: checked B1-B5 and edge cases (singleton covers and zero objects); repaired the statement so X, Y, E, K, and the open cover are introduced explicitly.
- `lem-pc-affine-qcoh-derived-equivalence`: checked against Lemma 36.3.5, Tag 06Z0; corrected the source tag from the chapter tag 08CU.
- `lem-pc-derived-module-free-generation`: checked against Remark 15.60.11, Tag 09PB, as invoked by 08EU; corrected the source and retained the stated closure formulation.
- `lem-pc-derived-direct-image-direct-sums`: checked against Lemma 36.4.5, Tag 08DZ; corrected the source from 08EU to the direct-sum lemma.

Changes: corrected all three Stacks tags, removed the invalid chapter-level external citation, completed the locality statement's hypotheses, and recorded the source correction for the imported item.

## Source error

The imported source list named Tag 08CU for the affine-equivalence input, but 08CU is the chapter page rather than a lemma. The precise affine-equivalence source is Tag 06Z0; the item itself is Tag 08EU.
