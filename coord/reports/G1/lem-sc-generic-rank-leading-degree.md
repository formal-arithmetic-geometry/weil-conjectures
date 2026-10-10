# Stage-1 report

## Files written

- `dag/nodes/sec-abelian-varieties/lem-sc-generic-rank-leading-degree.json`: repaired split item.
- `dag/nodes/sec-abelian-varieties/lem-sc-hilbert-polynomial-coherent-support.json`: statement-only unsplit node; Mathlib searches found no match.
- `citations.json`: verbatim citations for item proof step 1.

## Attachments

None. The matching declaration `AlgebraicGeometry.Scheme.Hom.fwdDiff_iter_eulerChar_tensorObj_tensorPow` is present in `WeilConjectures/AlgebraicGeometry/Modules/Ample.lean:651-658`, but its proof contains `sorry`.

## WANTED

None.

## Not duplicates

- `lem-sc-hilbert-polynomial-coherent-support` vs `lem-sc-hilbert-polynomial`: the existing node treats only the structure sheaf (and an ample module) on the whole proper scheme, while the new node treats arbitrary coherent sheaves and bounds degree by support dimension.
- `lem-sc-hilbert-polynomial-coherent-support` vs `lem-sc-deg-pullback-finite`: the existing node proves a finite-pullback degree formula and uses generic rank, while the new node is the independent coherent-sheaf Hilbert polynomial bound needed for the dévissage quotients.
- `lem-sc-hilbert-polynomial-coherent-support` vs `lem-sc-hilbert-difference`: the existing node gives one regular-section exact sequence and a forward-difference identity under no-embedded-points hypotheses, while the new node gives the general numerical-polynomial degree bound for every coherent sheaf by support dimension.

## Review by G1

I read `literature/stacks-project/varieties.tex`, Lemma 33.45.2 (Tag 0BEN), whose leading-term proof gives the generic-point length comparison, together with the finite-morphism application in Lemma 33.45.11 (Tag 0BEX) and the unit route in `sk-prop-av-deg-pullback`. I also read the existing `lem-sc-hilbert-polynomial` statement and verified that it supplies the ample-module polynomial input. The dévissage assertion is a clause of the item itself, so it is written directly in Step 1 rather than introduced as a duplicate node.

Step 1 uses only the two cited statements. Their hypotheses match the item: `Y` is proper of dimension `g`, `M` is ample, and `E` is coherent and free of rank `r` on a nonempty open. Adding the lower-degree difference to `r` times the Hilbert polynomial gives the asserted leading coefficient. Step 2 is elementary polynomial algebra: the `g`-th forward difference of a degree-at-most-`g` polynomial at zero is `g!` times its leading coefficient, so it gives the equivalent formal forward-difference formulation. I checked the edge cases `r = 0`, `g = 0`, and `E = M^{⊕ r}`; the statements reduce respectively to a zero difference, a constant polynomial, and equality by additivity.

I searched the whole DAG and blueprint for generic-rank Hilbert coefficient, dévissage, and Tag 0BEX variants. The only related existing node was `lem-sc-hilbert-polynomial`, which is cited. Mathlib searches for the item were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such by the search tool, while the other searches found no matching theorem.

## Second reading by G1

- Item statement: checked against Varieties Lemma 33.45.2 (Tag 0BEN), specialized to an integral scheme with generic rank r; the finite-morphism use is Lemma 33.45.11 (Tag 0BEX). Hypotheses and conclusion agree, including integral Y, nonempty generic-free locus, and dimension g.
- Step 1: checked the Hilbert-polynomial input against `lem-sc-hilbert-polynomial`, additivity against `lem-pc-euler-additive`, the coherent filtration against `lem-weil-pbc-coherent-filtration-integral-subschemes`, and the coherent-support bound against the new statement; expanded the generic-rank dévissage and marked it non-elementary, including the generic-point rank count and ideal short exact sequences.
- Step 2: checked as direct polynomial addition: a degree-at-most-(g-1) difference cannot change the m^g coefficient; no non-elementary dependency is used.
- New node: coherent-support Hilbert polynomial bound, self-contained with definition dependencies and recorded 0BEM source.
- Edge cases checked: r=0 gives zero leading coefficient, g=0 reduces to constants, and E=M^{⊕r} gives equality.
- Changes: repaired the invalid global injection argument, expanded Step 1 with the filtration/rank count and ideal sequences, added the filtration, Euler-additivity, and coherent-support dependencies with verbatim citation records, corrected the Stacks source from 0BEX to 0BEN, and corrected the item ownership metadata.
