# Stage 1 report: lem-pc-projective-space-canonical

## Files written

- `lem-pc-projective-space-canonical.json`: item split into four proof steps; no new nodes.
- `citations.json`: verbatim citations for every node used by every proof step.

## Attachments

None. The slopmaster2 declaration `AlgebraicGeometry.ProjectiveSpace.isFiniteLocallyFreeOfRank_relativeDifferentials` contains `sorry` and proves only the local-freeness clause; the module documentation marks the canonical-sheaf isomorphism as TODO.

## WANTED

None.

## What was checked and corrected

The item source is the projective-space canonical-sheaf blueprint node (order 620), and the Lean source is `WeilConjectures/AlgebraicGeometry/ProjectiveSpace/Differentials.lean`, lines 40--52. The Lean statement has a sorry and explicitly omits the exterior-power/twist construction, so it is not an attachment. I searched the whole DAG for the differential facts and found the existing nodes `lem-weil-pbc-kahler-differentials-localization` (Stacks 00RT) and `lem-weil-pbc-polynomial-ring-kahler-basis-any-variables` (Stacks 00RX); their statements give exactly the localization isomorphism and polynomial-ring bases used in step 1. I also read `def-pc-projective-space-twist` and `lem-pc-projective-space-twist-cohomology` to verify the transition rule and the rank-one top cohomology used in step 4.

Step 1 cites those two existing statements and checks the hypotheses by taking each chart ring to be a polynomial ring over A and each overlap ring to be its localization. This yields the canonical gluing identifications, local freeness of rank n, and the local wedge basis. Steps 2 and 3 are elementary calculations from the coordinate definitions: differentiating the inverse and quotient formulas, then discarding repeated `dt_i` terms in the alternating wedge and counting the permutation sign. Step 4 cites the twist's stated transition rule and the cohomology node's clause (ii); the computed overlap factor is exactly the twist factor, so the local maps glue and the n=1 formulas follow by substituting `s=t^{-1}`.

I tested the edge cases n=1 (the displayed `dt=-t^2 ds` calculation) and n=2 (the sign/permutation formula for a pair of charts); both agree with the stated transition factor. Mathlib searches were run for the item using LeanFinder, Loogle, grep, and LeanSearch. LeanFinder returned only projective-spectrum structure declarations, Loogle returned no usable hit (and reported its `exterior` identifier error), grep found no matching declaration, and LeanSearch was unavailable; these exact outcomes are recorded in `mathlib_searches`.

## Review by M1

I read the imported item, its blueprint proof text, the projective-space Differential.lean module, and every cited DAG statement. The first step's two citations say precisely that Kähler differentials localize and that polynomial-ring differentials are free on the coordinate differentials; no hidden result is used. The second and third steps are explicit two-line coordinate and wedge computations and are marked elementary. The fourth citation gives the twist transition rule verbatim, while the cohomology citation gives the rank-one `H^n(P,O(-n-1))` clause verbatim. I verified the hypotheses on every chart and overlap, checked the transition signs for n=1 and n=2, and corrected the imported proof by adding the missing node dependencies, changing all elementary flags from null, adding the cohomology dependency, and filling the blueprint, search, split-report, and citation records.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Second reading by M1

- Item statement: checked against the imported projective-space canonical-sheaf blueprint node (order 620), including all hypotheses on (A,n,P,U_i,R_i), the exterior-power construction, twist transition, cohomology clause, and the (n=1) specialization; verdict: agrees, with (n\ge1) intentionally excluding (n=0).
- Step 1: checked the localization and polynomial Kähler-basis node statements; their hypotheses apply to the chart polynomial rings and overlap localizations, and the triple-overlap compatibility is the canonical localization identification; verdict: dependencies and conclusion match.
- Step 2: checked directly on the overlap coordinates (t_i=x_i/x_j), including the inverse and quotient derivative formulas; verdict: elementary and correct.
- Step 3: checked the alternating-wedge calculation and permutation sign for (n=1) and (n=2) (including both orders of (i,j)); verdict: elementary and correct.
- Step 4: checked the twist node's transition rule and the cohomology node's rank-one top-cohomology clause; the local maps glue and the displayed (n=1) formula follows; verdict: cited statements say exactly what is used.
- New nodes: none; duplicate, self-contained-statement, source-tag, and Mathlib-leaf checks are therefore vacuous. The existing-node search for both differential facts was confirmed by DAG grep.
- Lean audit: the slopmaster2 declaration was reread at `Differentials.lean:40-52`; it is marked `sorry` and documents only local freeness, so it cannot close or attach this item.
- Changes made in this second reading: none to node or citation data; added this review record. Dry-run delivery preflight passed.
