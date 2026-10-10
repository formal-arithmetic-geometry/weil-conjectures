Files written:

- `dag/nodes/sec-smooth-purity/lem-fin-etale-normal-components.json`: statement split, no new nodes; Mathlib search found no exact theorem.

Attachments:

- None.

WANTED:

- None.

What was checked: the source is the blueprint node for Tag 033C. There is no declaration tagged `lem-fin-etale-normal-components` in the project Lean source. The first proof step uses the existing definition that etale morphisms are smooth of relative dimension zero and the existing normality ascent theorem for smooth ring maps; the affine-local passage is exactly the scheme convention. The second step uses the existing Mathlib leaf that a Noetherian scheme has finitely many irreducible components and the existing normal/integral definition. I checked that every cited node contains the quoted fact, recorded verbatim in `citations.json`, and that the hypotheses (Noetherian source, normal integral target, and local domain conclusion) are used at the indicated steps. The imported proof was corrected from one compressed paragraph into two complete arguments; no new node was created because all reusable facts already exist.

## Review by G1

I read the Tag 033C source reference and the statements of `def-weil-pbc-scheme-conventions`, `def-sbc-smooth-morphisms`, `lem-weil-pbc-smooth-over-normal-ring-normal`, `lem-weil-pbc-noetherian-finite-components`, and `def-sbc-normal-dominant-galois`. Step 1 takes exactly the etale-is-smooth clause and smooth normality ascent, then applies them affine-locally to the normal local rings of the target. Step 2 takes exactly finite irreducible components and the definition of normal integral schemes; disjointness follows because a local domain has one minimal prime, and finiteness makes complements closed. I tested the component argument on an integral target and on a disjoint union of two affine normal schemes; the conclusions are unchanged. The only correction was replacing the imported single paragraph with explicit steps and adding the required Mathlib search record and verbatim citation file.

## Second reading by G1

- Item statement: checked against the blueprint node and Stacks Tag 033C (normality ascends along smooth maps), with Noetherianity supplying quasi-compactness; hypotheses and conclusion agree.
- Step 1: checked the statements of `def-sbc-smooth-morphisms`, `lem-weil-pbc-smooth-over-normal-ring-normal`, and `def-weil-pbc-scheme-conventions`; the affine-local smooth-map argument gives normal-domain local rings and reducedness, with no uncited non-elementary claim.
- Step 2: checked `lem-weil-pbc-noetherian-finite-components` and `def-sbc-normal-dominant-galois`; the minimal-prime argument, closed-complement argument, and componentwise normality/integrality use exactly those statements and definitions.
- New nodes: none; therefore B1-B7 and duplicate/Mathlib-node checks are vacuous. Existing Mathlib leaf `lem-weil-pbc-noetherian-finite-components` was checked at its recorded declaration and line.
- Edge cases: an integral field scheme gives one component, a disjoint union of two normal affine schemes gives two open-and-closed components, and the empty Noetherian etale scheme is the empty finite disjoint union; the statement remains sound for all three.
- Changes: none to the node or citations; this section records the independent source, dependency, hypothesis, and edge-case checks required for delivery.
