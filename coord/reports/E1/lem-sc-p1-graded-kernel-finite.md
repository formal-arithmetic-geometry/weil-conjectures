Files written:

- `dag/nodes/sec-picard-framework/lem-sc-p1-graded-kernel-finite.json` — item, statement node, split proof.
- `dag/nodes/sec-picard-framework/lem-sc-p1-graded-submodule-finite.json` — new statement-only node; no Mathlib exact match.
- `citations.json` — verbatim citation for step 2.

Attachments:

- None.

WANTED: Hartshorne, Algebraic Geometry, II.5 (Hilbert basis theorem and graded-module Noetherianity), for `lem-sc-p1-graded-submodule-finite`.

What was wrong or incomplete in the imported item: it had no proof split. The imported Mathlib searches correctly indicated no graded formulation, but did not isolate the needed Noetherian graded-submodule statement as a DAG dependency; I added that statement-only node. The kernel-grading observation is elementary from the definition of a graded map and is written directly as step 1.

What I could not finish: no Lean declaration was available for this blueprint item, and the classical Hartshorne source is not present locally; the new dependency is therefore left `unsplit` with an agent-origin proof obligation for a later worker.

## Review by E1

I read the item node and the blueprint proof sentence in `lem-sc-p1-graded-resolution`; the item statement matches the stated two-variable polynomial-ring kernel claim and retains its `def-sc-p1-standard` dependency. I searched the whole DAG for Noetherian graded submodules, graded kernels, and the relevant blueprint phrase, and searched the Lean source for the item tag and related declarations; no existing exact node or sorry-free declaration was found. The new node is self-contained: it introduces `k`, `S`, `N`, and `K`, cites only the standard grading convention it uses, and states exactly the Noetherian graded-submodule fact needed by step 2.

Step 1 uses no non-elementary node: for a graded map, the homogeneous components of an element in the kernel map to the corresponding homogeneous components of zero, hence each lies in the kernel. Step 2 cites `lem-sc-p1-graded-submodule-finite`; its statement explicitly assumes a finitely generated graded module and a graded submodule and concludes finite graded generation, exactly matching `F` and `ker(q)`. The new node's Mathlib searches cover LeanSearch, Loogle, and a source grep; they found only ungraded Noetherian results, so it is not marked as a Mathlib leaf. I checked the edge cases `q=0` (kernel `F`) and `q=id` (kernel `0`), where the conclusion is immediate and consistent with the split.
