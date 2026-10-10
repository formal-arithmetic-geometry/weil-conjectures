files written:
- `dag/nodes/sec-nagata-compactification/thm-pqf-immersion-descent.json` — statement, split into four steps.
- `dag/nodes/sec-nagata-compactification/lem-pqf-qc-immersion-open-closed-factor.json` — statement, Mathlib leaf `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists_of_quasiCompact`.
- `citations.json` — verbatim quotes for every cited node in every item step.

attachments:
- `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists_of_quasiCompact` belongs to `lem-pqf-qc-immersion-open-closed-factor`.

WANTED: none.

what was wrong in the node, the blueprint, or the brief:
- The imported item had no proof and left the Tag 02LR normalization input and Tag 01QV factorization input undischarged. Tag 02LR is cited from the existing `pqf-lem-normalization-open` node; Tag 01QV is represented by the exact Mathlib factorization theorem.
- The proof now explicitly checks quasi-compactness of the composite immersion using quasi-separated intersections and closed-immersion base change, then checks quasi-compactness of the resulting open immersion by base change.

what I could not finish, and why:
- No additional unsplit node was needed: the existing normalization node already records the Tag 02LR input.

## Not duplicates
lem-pqf-qc-immersion-open-closed-factor vs thm-pqf-immersion-descent: the new node states the generic Tag 01QV factorization lemma, while the item applies it to the specific composite through a finite stage.
lem-pqf-qc-immersion-open-closed-factor vs thm-pqf-immersion-descent (external Tag 01QV): the external tag is cited in the item; the new node records its standalone statement and Mathlib match.

## Review by G1
I read the target source declaration and docstring in `WeilConjectures/Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`; the declaration is present but its proof is `sorry`, so it is not an attachment. I read the item blueprint proof and the source nodes `def-weil-pbc-scheme-conventions`, `pqf-def-quasifinite`, `pqf-lem-limit-qc-open-descends`, `pqf-lem-limit-immersion-descends`, `pqf-lem-qs-intersection-qc`, `pqf-def-locnoeth`, and `pqf-lem-finite-fp-locnoeth`. Step 1 uses the finite-stage convention, the everywhere quasi-finite hypothesis, the new Tag 02LR statement, and the three-clause open descent statement; their quoted sentences state respectively finite stages, quasi-finiteness, the quasi-compact open normalization map, and descent of a quasi-compact open. Step 2 uses the finite-type convention for local finite type and the existing closed-immersion spreading statement, whose quoted conclusion is exactly eventual closed immersion. Step 3 uses the existing quasi-separated intersection statement and the new factorization statement; I checked that the composite is an immersion, that preimages of quasi-compact opens are closed subschemes of quasi-compact intersections, and that the open factor is a base change. Step 4 uses the locally Noetherian definition and the finite-over-locally-Noetherian finite-presentation lemma, matching the final clause. I ran the required Mathlib searches for the item and both new nodes, including LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such. I tested the statements against the exact source hypotheses and corrected the imported proof by making both recorded inputs explicit and by adding all proof dependencies and verbatim citation quotes.

## Second reading by G1
Step 1: checked against the blueprint Step 1, `pqf-lem-normalization-open`, and `pqf-lem-limit-qc-open-descends`; verdict: all finite-stage, quasi-compact-open, and limit hypotheses are present and cited.
Step 2: checked against blueprint Step 2, `def-weil-pbc-scheme-conventions`, and `pqf-lem-limit-immersion-descends`; verdict: the closed-immersion spreading conclusion and local finite-type input match.
Step 3: checked against blueprint Step 3, `pqf-lem-qs-intersection-qc`, Tag 01QV, and Mathlib's factorization declaration; verdict: the composite's quasi-compactness argument and open/closed factorization are stated explicitly.
Step 4: checked against blueprint Step 4, `pqf-def-locnoeth`, and `pqf-lem-finite-fp-locnoeth`; verdict: the locally Noetherian finite-presentation refinement matches.
New node `lem-pqf-qc-immersion-open-closed-factor`: checked B1-B7, Tag 01QV, and the Mathlib declaration at `Mathlib/AlgebraicGeometry/Morphisms/Immersion.lean:267`; verdict: self-contained exact factorization statement and valid Mathlib leaf.
Item node `thm-pqf-immersion-descent`: checked its hypotheses and conclusion against the blueprint/source, including empty, zero, field, and vacuous quasi-finite cases; verdict: no statement weakening or false edge case found.
Changed `citations.json` Step 4's `pqf-def-locnoeth` quote to the node's complete verbatim statement after the dry run rejected the abbreviated quote; no mathematical statements or proof steps were changed.
Dry-run delivery passed preflight after this citation repair.
