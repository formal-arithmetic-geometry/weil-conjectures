Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-affine-unit-quotient.json`: statement, split proof, no Mathlib match.
- `citations.json`: exact quotes for all four cited nodes in step 1.

Attachments: none.

WANTED: none.

The existing Lean theorem `AlgebraicGeometry.IsConnectedCurve.finite_units_quotient` has the matching statement but is not an attachment because its transitive audit includes the sorry-backed declaration `AlgebraicGeometry.Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H`. The imported natural-language proof is therefore retained and marked split. No new node was necessary: the proof uses the already existing compactification, divisor-class, global-functions, and curve-definition statements. The item itself was searched in Mathlib with LeanFinder, Loogle, grep, and LeanSearch; no matching Mathlib theorem was found (LeanSearch was unavailable).

## Review by C1

I read the item source and its blueprint proof paragraph, then opened every cited node. The compactification node states exactly the proper smooth compactification with finite closed-point complement used in step 1. The divisor-class node states the divisor/Picard identification for smooth connected curves, and the global-functions node states that global functions on a proper connected curve are exactly $k$; these are the precise facts used to identify the kernel of the divisor map with $k^\\times$. The curve-definition node supplies the algebraically closed, smooth, affine, connected hypotheses and was added to the proof uses and proof dependencies because the step relies on those definitions.

I checked the hypotheses: the item gives an algebraically closed field and a smooth affine connected curve, so compactification applies; its boundary is finite, making the direct sum of divisor generators finite rank; algebraic closedness supplies an $n$-th root for every constant. The remaining subgroup and quotient arguments are elementary abelian-group calculations from the displayed construction. I tested the edge cases $n=1$ (the quotient is trivial) and $C=\\mathbf A^1_k$ (units are $k^\\times$, so the quotient is trivial). The only correction was adding the previously omitted `def-sc-curves` citation; no statement or source claim was changed.

## Second reading by C1

- Item statement: checked against the blueprint node and `def-sc-curves`; the smooth affine connected curve and $n\\ge1$ hypotheses and finite quotient conclusion agree.
- Step 1: checked compactification against `lem-sc-compactification`; checked the divisor kernel and valuation criterion against `lem-sc-divisor-sequence-general`, finite support against `lem-sc-divisor-finite-support`, constants against `lem-sc-global-functions`, and the finite-free subgroup claim against `lem-weil-subgroup-finite-free-abelian-group-free`; verdict: complete after repair.
- Edge cases: $n=1$ gives the trivial quotient; for $C=\\mathbf A^1_k$, units are $k^\\times$; the argument also applies to a proper curve with empty boundary.
- New nodes: none; existing nodes were searched in `dag/nodes` and the Mathlib search log, so no duplicate or elementary node was retained.
- Changed the proof to remove the unsupported `lem-sc-divisor-class-curve` citation, add the existing divisor-sequence, finite-support, and finite-free-subgroup dependencies, and spell out finite reduction modulo $n$ and the injectivity argument.
- Updated `citations.json` with verbatim statements for all added citations.
