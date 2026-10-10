# Stage-1 report: thm-sc-affine-cohomology

## Files written

- `dag/nodes/sec-curve-estimates/thm-sc-affine-cohomology.json`: statement, two-step proof, blueprint placement, searches, and split report; no new nodes.
- `citations.json`: verbatim node-statement quotes for every cited dependency in each step.

## Attachments

None. The declaration `AlgebraicGeometry.IsConnectedCurve.sheafH_constantZMod_of_isAffine` in `WeilConjectures/AlgebraicGeometry/Curve/CohomologicalDimension.lean:527-573` was read and rejected as an attachment because it gives only a `Nonempty` degree-zero equivalence and an existential exact sequence ending in torsion of `C.CohomologicalPicardGroup`, whereas this item requires the canonical trivialization and an exact sequence ending in `Pic(C)[n]`.

## WANTED

None.

## Problems found

The prior Lean declaration does not state the blueprint theorem exactly, so it cannot close this item. The existing imported proof also expanded the Kummer argument directly while omitting the already-existing `lem-sc-kummer-les` node. I replaced that expansion with a citation to the precise short exact sequence and H² cokernel statement, then separately cited the affine Picard and unit finiteness lemmas and the affine cohomological-dimension lemma. No duplicate node was created: each required fact already exists in the DAG.

## Second reading by M1

- Item statement: checked against `thm-sc-affine-cohomology`, including smooth affine connected curve hypotheses, `n` invertible in `k`, the `\theta_\zeta` transport, unit quotient and `\operatorname{Pic}(C)[n]` finiteness, the short exact sequence, and vanishing for `q>1`; verdict: agrees.
- Step 1: checked `lem-sc-kummer-les` (exact sequence, `H^0`, and `H^2` cokernel), `lem-sc-brauer-zero` (Brauer vanishing), `lem-sc-primitive-root` and `def-sc-mu-trivialization` (root and sheaf transport), `lem-sc-affine-unit-quotient` (unit finiteness), and `lem-sc-pic-affine` (Picard divisibility and finite torsion); verdict: every non-elementary use is stated by a cited node.
- Step 2: checked against `lem-sc-affine-cohomological-dimension`; its torsion etale-sheaf conclusion applies to constant `\mathbf F_n`; verdict: exact specialization.
- New nodes: none; B1-B7 and duplicate-node checks are vacuous. Existing-node searches found all seven cited facts, and no Mathlib leaf was introduced.
- Edge cases: `C=\mathbf A^1` has trivial unit quotient and Picard group; `n=1` gives the zero constant sheaf and the displayed exact sequence with zero end terms; connected curve hypotheses exclude the empty scheme.
- Changes made: added this second-reader audit; no mathematical statement or dependency required repair.

## Review by M1

I read the blueprint source `literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd-affine/thm-sc-affine-cohomology.md`, the target node, and the Lean source around the rejected declaration. The item hypotheses are exactly those used by the cited statements: smooth, affine, connected curve over algebraically closed `k`, and `n` prime to the characteristic. In step 1, `lem-sc-kummer-les` supplies the canonical short exact sequence and the H² cokernel formula under `H²(C,G_m)=0`; `lem-sc-brauer-zero` supplies that vanishing; `lem-sc-primitive-root` and `def-sc-mu-trivialization` supply the root and canonical sheaf identification; `lem-sc-affine-unit-quotient` supplies finiteness of the unit quotient; and `lem-sc-pic-affine` supplies divisibility and finite `Pic(C)[n]`, so the H² cokernel is zero. Step 2 applies the exact statement of `lem-sc-affine-cohomological-dimension` to the torsion constant sheaf. I opened every cited node and copied the relevant sentences into `citations.json`; the quotes are verbatim. I checked small cases conceptually: for `C=A¹`, the unit quotient is zero and `Pic(C)=0`, so the sequence reduces to `H¹=0` and higher groups vanish. The only correction to the imported item was replacing its direct, partially duplicated Kummer proof with the existing exact-sequence node and recording the required blueprint/search metadata.
