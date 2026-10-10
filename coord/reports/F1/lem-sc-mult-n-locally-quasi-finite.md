# Stage 1 report

1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-mult-n-locally-quasi-finite.json`: statement split into four steps; Mathlib verdict no exact item theorem.
- `dag/nodes/sec-abelian-varieties/lem-sc-mult-n-dim-one-closed-subscheme.json`: statement, closed project declaration `AlgebraicGeometry.Scheme.exists_isClosedImmersion_topologicalKrullDim_eq_one` in `WeilConjectures/Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean:205-207`; upstream Mathlib searches had no match.

2. Attachments: `AlgebraicGeometry.Scheme.exists_isClosedImmersion_topologicalKrullDim_eq_one` belongs to `lem-sc-mult-n-dim-one-closed-subscheme`. The item declaration `AlgebraicGeometry.locallyQuasiFinite_npow_id_of_isAlgClosed` was checked at `WeilConjectures/AlgebraicGeometry/AbelianVariety/Isogeny.lean:73-134`; it is not attachable because its transitive proof graph rests on sorry declarations.

3. WANTED: none.

4. The original item had no proof split. I retained its statement and traced the source paragraph: openness of the quasi-finite locus, a positive-dimensional fibre, extraction of a dimension-one closed subscheme, and the ample-degree contradiction. I searched the whole DAG and blueprint before creating the dimension-one node; no existing node stated the exact Mathlib theorem. The existing node `lem-sc-ample-positive-degree` already supplies positivity on a proper one-dimensional curve, so no duplicate positivity node was created.

## Review by F1

I read the item source paragraph in `literature/blueprint/master/blueprint/sec-abelian-varieties/sk-prop-av-mult-finite/_section.md` and the Lean docstring and body for `locallyQuasiFinite_npow_id_of_isAlgClosed`. Step 1 uses the existing statement that the quasi-finite locus is open and verifies the abelian variety is proper; step 2 checks that failure of quasi-finiteness gives a non-discrete locally Noetherian fibre of finite dimension; step 3 uses the exact Mathlib theorem recorded in the new leaf and checks that pullback of an ample module remains ample; step 4 uses the existing ample-positive-degree statement and the elementary tensor-power degree calculation to contradict triviality. Every cited node was opened and its quoted sentence was copied verbatim into `citations.json`. I also verified the new Mathlib declaration and source line, ran all required `msearch.py` searches for both the item and new leaf, and corrected the abelian-variety citation quote to match the repository exactly.

5. Nothing remains unfinished in the split; the delivery dry run is the remaining gate.

## Second reading by F1

- Item statement: checked the algebraically closed field, abelian-variety, positive-integer, and locally-quasi-finite hypotheses against the Lean declaration and the blueprint Step 1; verdict: statement retained.
- Step 1: checked the open quasi-finite locus and proper abelian-variety hypotheses against `lem-sc-quasi-finite-points-open` and `def-sc-abelian-variety`; verdict: retained with the closed-point reduction stated explicitly.
- Step 2: checked the fibre and non-discrete-point argument against the source proof and the Lean body; verdict: retained, with the local-Noetherian and finite-dimension implications written out.
- Step 3: checked the dimension-one closed-subscheme declaration and symmetric-ample construction; verdict: added citations to `lem-sc-ample-tensor` and made properness and pullback ampleness explicit.
- Step 4: checked the constant-fibre factorization, tensor-power isomorphism, and degree contradiction against `lem-sc-mult-n-pullback` and `lem-sc-ample-positive-degree`; verdict: added both citations and the degree calculation.
- New node `lem-sc-mult-n-dim-one-closed-subscheme`: checked its self-contained scheme and dimension hypotheses, exact project declaration, source lines, and recorded searches; verdict: valid unsplit attached declaration.
- Existing `lem-sc-ample-positive-degree`: checked that it is cited as an existing statement rather than delivered as a new node; verdict: no duplicate created.

Changes made: repaired the proof dependency union, added the missing symmetric-ample and multiplication-pullback citations and verbatim quotes, and expanded the four steps so the fibre and tensor-power arguments are not hidden behind “similarly” or “transports”.
