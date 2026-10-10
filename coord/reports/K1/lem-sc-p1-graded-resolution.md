Files written:

- `dag/nodes/sec-picard-framework/lem-sc-p1-graded-resolution.json` — statement, split into four cited ingredients; Mathlib search found no matching theorem.
- `dag/nodes/sec-picard-framework/lem-sc-p1-coherent-proj-representation.json` — statement-only node; Mathlib search found no matching theorem.
- `dag/nodes/sec-picard-framework/lem-sc-p1-graded-syzygy.json` — statement-only node; Mathlib search found no matching theorem.
- `dag/nodes/sec-picard-framework/lem-sc-p1-proj-sheafification-exact.json` — statement-only node; Mathlib search found no matching theorem.
- `dag/nodes/sec-picard-framework/lem-sc-p1-proj-shifted-free-twist.json` — statement-only node; Mathlib search found no matching theorem.

Attachments:

- None. `AlgebraicGeometry.ProjectiveLine.exists_exact_sigma_twist` in `WeilConjectures/AlgebraicGeometry/ProjectiveSpace/Duality.lean:77-94` still has `sorry`.

WANTED:

- EGA II, §2 or Hartshorne II.5 for the coherent-sheaf/graded-module correspondence on `Proj`, graded Hilbert syzygy in two variables, exactness of the associated-sheaf construction, and `\\widetilde{S(d)} \\cong \\mathcal O(d)`.

What was wrong in the imported node:

- The imported proof used the coherent-sheaf/graded-module correspondence, graded Hilbert syzygy, exactness of sheafification, and the shift/twist identification without separate cited statements. I made each a child node and cited all four in the item's proof. The item's statement also uses the meaning of coherent module, so `pqf-def-coherent` is now a statement dependency.
- The blueprint's source names EGA II and Hartshorne but the repository contains no local copy; the proof origin remains agent-written from that blueprint text, with the missing sources recorded above.

What I checked:

- I read the item's blueprint node and `sk-thm-picard-duality` unit. The item statement agrees with the blueprint: a coherent module on `Proj k[x_0,x_1]` receives a five-term exact resolution by finite sums of twists.
- For the representation node, I checked that `k` is a field, `S` is the standard graded polynomial ring, `P=Proj S` is introduced, coherence is cited to `pqf-def-coherent`, and `\\widetilde M` is defined by degree-zero localizations. Its small test cases are `\\mathcal G=0` (take `M=0`) and `\\mathcal G=\\mathcal O(d)` (take `M=S(d)`).
- For the syzygy node, I checked that the ring has exactly two polynomial variables and that finite generation and grading are explicit. The cases `M=0` and `M=S(d)` admit the displayed resolution with zero higher terms, so the length bound is consistent at the edges.
- For exact sheafification, I checked that all maps are degree-preserving and that exactness is asserted after localization on every standard homogeneous open. The zero sequence and a split short exact sequence remain exact after localization, testing the statement's boundary cases.
- For the shift/twist node, I checked that the standard affine cover and twists are supplied by `def-sc-p1-standard` and `lem-sc-p1-twist-exists`, and that finite direct sums are covered by additivity. The cases `d=0`, `d=1`, and a one-summand direct sum agree with the defining transition functions.
- The rewritten proof follows the blueprint paragraph in order: represent `\\mathcal G`, resolve `M`, sheafify exactly, then identify shifted frees with twists. Every non-elementary step cites a node whose statement supplies the fact used; the only elementary operation is substituting the resulting isomorphism into the final term.
- I searched the DAG for all four ingredients before creating nodes, searched the blueprint with `tools/blueprint_refs.py`, searched Lean locally for the source declaration, and ran JSON validation plus `tools/check_dag.py`; the latter found no cycles or self-loops.

## Review by K1

I reviewed the item against `literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-duality/lem-sc-p1-graded-resolution.md` and the unit record `dag/units/sk-thm-picard-duality.json`. The source's single proof paragraph requires four independent facts, so the item now cites `lem-sc-p1-coherent-proj-representation`, `lem-sc-p1-graded-syzygy`, `lem-sc-p1-proj-sheafification-exact`, and `lem-sc-p1-proj-shifted-free-twist` in that order. Each cited statement says exactly what its proof step takes: existence of `M` and `\\widetilde M\\cong\\mathcal G`; a length-two graded free resolution; preservation of exactness under associated sheafification; and `\\widetilde{S(d)}\\cong\\mathcal O(d)`. The representation node cites the existing coherent-module definition, and the shift node cites the existing standard-cover and twist-existence nodes. I checked hypotheses explicitly in each node, tested zero and one-summand cases, and corrected the imported proof's missing coherent dependency and uncited substantive arguments. The source documents for the classical facts are unavailable locally, so they are marked `WANTED` rather than silently treated as Mathlib results.
