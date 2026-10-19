# Stage-1 report: lem-a1-constituent-nonexceptional-comparison

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-constituent-nonexceptional-comparison.json`: item split; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-geometric-constant-trivial-constituent.json`: statement-only supporting lemma; Mathlib searches found no match.
- `citations.json`: verbatim statement excerpts for every cited node in every item proof step.

## Attachments

None. The two matching declarations in `WeilConjectures/DeligneLaumon/AffineLine/MiddleExtension.lean` are sorry-backed transitively, so they are not attachments.

## WANTED

None.

## Source and DAG issues

The imported item proof used the contrapositive for the first implication and did not cite the existing dense-open lisse recovery theorem. I rewrote the steps so the translation of Fourier-exceptionality is explicit, then proved the first implication by contradiction and the converse under geometric irreducibility. The item statement itself agrees with the current blueprint and was not changed. The source theorem `hasLinearArtinSchreierConstituent_zero_of_isGeometricallyConstant` is present at lines 100–108 of `MiddleExtension.lean` but has a `sorry`; I represented its needed content as the new unsplit node rather than treating the declaration as finished.

## Review by Q100

I read the item node, its source text in `literature/blueprint/master/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-middle/lem-a1-constituent-nonexceptional-comparison.md`, the current Lean source `WeilConjectures/DeligneLaumon/AffineLine/MiddleExtension.lean` (including both comparison declarations and the constant-constituent theorem), the unit `sk-p-dl-a1-middle`, and the chapter record. I also read the complete statements of `def-a1-constituent-nonexceptional`, `def-fd-nonexceptional`, `def-wf-middle-extension`, `def-wf-constant-weil-twist`, and `lem-a1-lisse-middle-extension`; the quotes in `citations.json` are copied verbatim from those statements.

Step 1 uses the Fourier-nonexceptional definition, the ordinary middle-extension definition, the constant-twist definition, and `lem-a1-lisse-middle-extension`. The latter says that for a lisse sheaf on the whole curve the unit to `j_*j^*` is an isomorphism, exactly what is needed for constant and Artin–Schreier sheaves on the affine line. The restriction `j^*j_*M=M` follows directly from the section formula in the cited middle-extension definition. I checked that the Fourier definition's second alternative includes geometric irreducibility and an Artin–Schreier constituent, while the constant-twist clause concerns only the underlying geometric sheaf.

Step 2 uses the new node for the constant case and the two nonexceptionality definitions. The new node states precisely that a nonzero geometrically constant sheaf has the trivial rank-one constituent; its hypotheses are met because the item assumes `M` is nonzero. In the Artin–Schreier case, the Fourier definition itself states that the sheaf is geometrically irreducible and that the Artin–Schreier sheaf is a constituent, so the constituent definition gives the contradiction. Step 3 uses the Jordan–Hölder constituent definition and the Fourier definition. Under geometric irreducibility, the representation has itself as its sole constituent, an elementary one-line Jordan–Hölder fact; an exceptional constituent therefore identifies `M` with the corresponding Artin–Schreier restriction, and Step 1 makes the middle extension Fourier-exceptional.

I checked the edge cases `a=0`, a nonzero constant sheaf, a linear Artin–Schreier sheaf, and a geometrically irreducible non-linear sheaf. The first two are correctly excluded by constituent-nonexceptionality; the converse is asserted only under geometric irreducibility. The new node was searched in the DAG and blueprint before creation; no duplicate or Mathlib theorem states it. The only off-unit citation is `lem-a1-lisse-middle-extension`, declared in `split_report.tool_uses` because it supplies the generic lisse-extension fact used in Step 1.
