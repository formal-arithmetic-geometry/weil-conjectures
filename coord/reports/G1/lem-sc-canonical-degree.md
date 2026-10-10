# lem-sc-canonical-degree

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-canonical-degree.json`: split; the item is not a Mathlib leaf.
- No new nodes remain in this repaired delivery.

## Attachments

- `AlgebraicGeometry.Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H` belongs to `lem-pc-cohomology-sections-affine-base`.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage` belongs to `lem-pc-finite-support-hi` (its first clause).
- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_topologicalKrullDim_lt` belongs to `lem-sc-noetherian-cohomology-above-dimension` for quasi-coherent modules.
- `finite_sections_higherDirectImage` belongs to `lem-pc-coherent-hi`, and `ProjectiveSpace.subsingleton_H_of_lt` belongs to `lem-pc-projective-space-cohomology-bound`.
- IsFiniteLocallyFree.dual, IsFiniteLocallyFree.tensorObj, nonempty_iso_dual_tensorObj_dual_tensorObj: open obligations of thm-sc-serre-duality-curve (cited in step 2), left to its split.
- exists_isIso_pushforwardHomObjComparison_unit belongs to lem-sc-finite-duality.

## WANTED

- WANTED: local `literature/stacks-project/curves.tex`, Tags 0BS2 and 0BS6, for `lem-sc-canonical-degree`. This checkout contains the citation table but no fetched Stacks source. I read both official tag pages online.
- WANTED: the local blueprint file under `literature/blueprint/master/` for the item. Its imported proof text and unit record are present in the DAG.

## Corrections and limits

- The original item used an unintroduced $K_C$ and wrote equality of sheaves where the intended assertion is an isomorphism. I stated existence of a divisor and independence of its degree from the chosen divisor. The proper smooth connected curve is explicitly one-dimensional.
- The tagged Lean declaration `AlgebraicGeometry.Scheme.degree_relativeDifferentials` proves only the degree of relative differentials and transitively rests on sorries. It does not state the divisor-existence clause, so it is not an exact attachment.
- The returned delivery added four nodes for transitive Lean obligations that no step of this item uses. I removed them; their owners are identified under Attachments.

## Review by G1

I read Stacks Tags 0BS2, part (6), and 0BS6, parts (1) and (2), against the item's statement. The first identifies the dualizing sheaf of a smooth curve with differentials; the second makes it invertible and computes its degree from the structure-sheaf Euler characteristic. I checked the imported item proof and unit Step (RR) against those claims. The local Stacks and blueprint source files were unavailable as recorded above.

Step 1 uses `lem-sc-canonical-sheaf` for invertibility, `lem-sc-smooth-connected-curve-local-rings` for integrality, and `lem-sc-line-bundle-rational-section` for a divisor of a nonzero rational section and the resulting line-bundle isomorphism. Step 2 uses `lem-sc-global-functions` for $H^0(\mathcal O_C)=k$, `def-sc-genus` for $h^1=g$, `thm-sc-serre-duality-curve` with $\mathcal M=\mathcal O_C$ for the two cohomology dimensions of $\omega_C$, and `lem-sc-noetherian-cohomology-above-dimension` to reduce each Euler characteristic to dimensions zero and one. The item's properness, smoothness, connectedness, algebraically closed base, and dimension-one hypotheses supply the hypotheses of these statements; the structure sheaf is finite locally free. Step 3 invokes the line-bundle clause of `lem-sc-riemann-roch` for the invertible canonical sheaf and solves the resulting integer equality. Step 4 applies `def-sc-pic0`, whose degree definition gives $\deg[\mathcal O_C(D)]=\deg D$; the divisor was produced in Step 1.

For return point 1 (D and B9), I checked the four added statements against every step and found no citation or use. `thm-sc-serre-duality-curve` carries the dual, tensor, and twisted-biduality declarations among its open Lean obligations; `lem-sc-finite-duality` carries the trace comparison. I removed their files and the claims that they are premises of this item. There are now no new statements in this delivery requiring independent source or small-case checks. For return point 2 (C8), I removed `lem-sc-line-bundle-rational-section` from `split_report.tool_uses`: it belongs to this item's unit. The remaining three entries name inputs from other units and state what each supplies. I checked the retained four steps for missing cited facts, cycles, and unverified hypotheses. The earlier correction of the unbound divisor and equality/isomorphism mismatch remains.
