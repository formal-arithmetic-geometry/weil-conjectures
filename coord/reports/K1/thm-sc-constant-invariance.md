## Files written

- `dag/nodes/sec-curve-estimates/thm-sc-constant-invariance.json`: repaired item split.
- `dag/nodes/sec-curve-estimates/lem-sc-proper-or-affine.json`: new unsplit statement node; Mathlib searches no match.
- `dag/nodes/sec-curve-estimates/lem-sc-units-quotient-base-change.json`: new unsplit statement node; Mathlib searches no match.
- `dag/nodes/sec-curve-estimates/lem-sc-kummer-base-change-compatibility.json`: new unsplit statement node; Mathlib searches no match.
- `citations.json`: updated verbatim citations for all repaired proof steps.

## Attachments

None.

## WANTED

None.

## Not duplicates

lem-sc-proper-or-affine vs lem-sc-proper-dim-one-projective: both cite Stacks 0A26, but the new node states the proper-or-affine dichotomy for smooth separated connected curves, whereas the existing node states projectivity of an already proper dimension-at-most-one scheme.

## What was repaired

The prior delivery incorrectly took connectedness of `C_{k'}` directly from `lem-sc-base-change-curve`, treated every smooth separated connected curve as already in the proper or affine case, used `lem-sc-brauer-zero` to claim vanishing of `H^2(C, mu_n)`, and left unit-quotient and Kummer/degree compatibility as uncited inline assertions. I added the three statement-only nodes above, cited the existing `lem-weil-separably-closed-geometrically-connected` node for connectedness, replaced the H^2 argument by `lem-sc-affine-cohomological-dimension`, and removed the unused `lem-sc-pic-proper-ntorsion` statement dependency.

## Review by K1

I reread the blueprint proof and the statements of `lem-sc-base-change-curve`, `lem-weil-separably-closed-geometrically-connected`, `lem-sc-affine-cohomological-dimension`, `lem-sc-kummer-les`, `lem-sc-pic-affine`, `thm-av-final`, `thm-sc-jacobian-representability`, and the existing proper-cohomology and genus nodes. Step 1 now takes smoothness and separation from the base-change node and connectedness from the separably-closed geometric-connectedness equivalence, with the hypotheses checked explicitly. Step 2 uses the new Kummer compatibility statement for the naturality claim, together with the proper cohomology, primitive-root, genus, Jacobian, abelian-variety, and Kummer statements; each cited statement supplies the group or map used. Step 3 first invokes the new proper-or-affine dichotomy, then uses the Kummer and Picard quotient statements, the new units base-change statement, and the new degree compatibility statement. Its H^2 and higher-degree conclusion now follows from the affine cohomological-dimension statement, which applies to torsion etale sheaves and therefore to `mu_n` and `F_n`.

For each new node I searched the whole DAG and blueprint for duplicates before writing it, then ran LeanFinder, Loogle, grep, and LeanSearch searches; LeanSearch was unavailable and recorded as such. I tested the repaired case split on proper curves and on affine examples such as `A^1` and `G_m`; the unit quotient statement is consistent with these cases (`k^x/k^{x n}=0` for algebraically closed `k`, and the boundary divisor description for `G_m`). The citations file quotes literal text from every cited node statement. The previous return points are each addressed directly: connectedness, proper/affine dichotomy, H^2(mu_n) vanishing, units invariance, and Kummer/degree compatibility.

## Second reading by K1

- Step 1 checked against `lem-sc-base-change-curve` and `lem-weil-separably-closed-geometrically-connected`; verdict: hypotheses and connectedness after base change are explicit.
- Step 2 checked against `thm-sc-proper-cohomology`, `lem-sc-primitive-root`, `lem-sc-genus-invariant`, `thm-av-final`, `thm-sc-jacobian-representability`, `lem-sc-kummer-les`, and the compatibility node; verdict: proper-case identifications and naturality are cited.
- Step 3 checked against `lem-sc-proper-or-affine`, `lem-sc-kummer-les`, `lem-sc-units-quotient-base-change`, `lem-sc-kummer-base-change-compatibility`, and `lem-sc-affine-cohomological-dimension`; verdict: affine H0, H1, H2, and higher-degree cases are covered.
- `lem-sc-proper-or-affine` checked against Stacks Lemma 0A26 and proper/affine curve cases; verdict: self-contained statement-only dichotomy.
- `lem-sc-units-quotient-base-change` checked against the blueprint unit-divisor argument, compactification and Jacobian dependencies, and affine examples; verdict: statement is the required quotient invariance.
- `lem-sc-kummer-base-change-compatibility` checked against the blueprint Kummer naturality and affine Picard-torsion argument; verdict: corrected to state `Pic(C)[n]` invariance, since `lem-sc-pic-affine` makes `Pic(C)/n` divisible and does not give an affine degree quotient.

Changes made: corrected the false affine `Pic(C)/n` degree-map assertion; updated step 3 and citations to use affine Picard torsion; recorded this second reading and edge-case checks.
