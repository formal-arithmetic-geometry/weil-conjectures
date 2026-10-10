# Stage-1 worker report: lem-sc-very-ample-separation-criterion

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-very-ample-separation-criterion.json`: split into four proof steps; added the missing divisor-module statement dependency.
- `dag/nodes/sec-picard-framework/lem-sc-point-tangent-separation-closed-immersion.json`: new unsplit statement of Stacks Tag 0E8S, with the complete-linear-system conclusion and the Tag 02O5 proper-coherent finiteness prerequisite; no Mathlib match (LeanSearch HTTP 500, Loogle empty, Mathlib source grep empty). Added explicit base-point-free hypothesis (0) and the generating-sections dependency.

## Attachments

None. `AlgebraicGeometry.Scheme.isVeryAmple_of_finrankH_zero_tensorObj_toModules_ker` in `WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch.lean:1418` is sorry-free directly and transitively in the 71d63dcf map, but its formal conclusion is the existential `AlgebraicGeometry.IsVeryAmple`. The item cites `def-sc-ample`, whose conclusion requires the *complete* linear system to be a closed immersion. The Lean proof constructs that immersion from a full basis, but this strengthening is not the declaration's formal conclusion. I therefore did not report an exact attachment.

## Sources wanted

WANTED: `literature/stacks-project/varieties.tex`, Tag 0E8S (lemma-separate-points-tangent-vectors), for `lem-sc-point-tangent-separation-closed-immersion` and steps 1 and 4 of the item. This literature file was not present in the E1 checkout. I read the published Stacks Tag 0E8S page and used its label, statement and proof, but under the stage-1 rule the item's `proof_origin.by` is `agent` until the literature file is obtained.

WANTED: `literature/stacks-project/coherent.tex`, Tag 02O5 (proper coherent cohomology), for the finite-dimensionality clause of `lem-sc-point-tangent-separation-closed-immersion`. The source tree is absent in E1; the existing node `lem-pc-coherent-hi` records the tag.

WANTED: `literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-rr/lem-sc-degree-2g1-very-ample.md`, proof paragraphs 2 and 3, for steps 2 and 3 and the new node's blueprint reference. The blueprint tree was not present in the E1 checkout; the imported parent node retains these paragraphs in its step text.

## Problems found

The imported item cited `def-sc-pic0` as if it defined the twists by point divisors; that node defines degree, while `def-sc-divisor` defines the associated divisor module. I made the twist explicit in the statement and added `def-sc-divisor` to `stmt_deps`. The item had no proof. The Lean theorem above is close but does not formally state the complete-linear-system conclusion. Stacks 0E8S states exactly the point-and-tangent separation fact needed after translating the dimension drops. The returned review identified a genuine gap in the auxiliary criterion: conditions (1) and (2) do not imply generation when there is only one closed point. Following E7, I added hypothesis (0), cited `def-weil-pbc-generating-sections`, and dropped generation from the conclusion. I also repaired item step 4 to state explicitly: "Step 1 gives (0), steps 2 and 3 give (1) and (2)."

## Unfinished work

The new Stacks criterion remains an unsplit node, as required for a one-level split. Its proper-coherent finiteness clause will need Tag 02O5 when the new node is split. No Lean was written or compiled.

## Review by E1

I read the item's imported statement, the parent `lem-sc-degree-2g1-very-ample` proof steps and unit `sk-thm-picard-rr`, the Stacks 0E8S page (Lemma 33.23.1), the Lean theorem at RiemannRoch.lean:1418-1511 and its conclusion's definition in Modules/Ample.lean:113-115. The item has precisely Stacks' properness, algebraic closure and invertibility hypotheses, plus smoothness and connectedness to interpret repeated points on a curve; the new node states Stacks' two separation hypotheses and its canonical-morphism conclusion. Its finite-dimensionality clause is the proper-coherent theorem Tag 02O5, needed to use the full section space. I searched the whole DAG and blueprint index for Tag 0E8S and point/tangent separation before creating it; neither has a node with Stacks' statement. The Mathlib grep and Loogle results are recorded in the new node, and LeanSearch failed with HTTP 500.

For step 1 I checked that `def-sc-divisor` defines $\mathcal O_C(-P)$ locally by vanishing to order at least one, so the first dimension drop gives a codimension-one kernel of evaluation. The evaluation is nonzero, including on $\mathbf P^1$ with $\mathcal O(1)$, where it has a two-dimensional section space. The new criterion's conclusion provides finite-dimensionality of the full section space from properness, coherency of the invertible module and Tag 02O5; I moved this prerequisite there after preflight identified `lem-pc-coherent-hi` and `pqf-lem-coherent-ft-locnoeth` as off-unit citations.

For step 2 I checked the *ordered* pair $P\ne Q$: `def-sc-divisor` identifies the nested spaces with vanishing at $P$, then at both $P$ and $Q$. Their stated codimensions are one and two, so a section in their difference vanishes at $P$ and not at $Q$. This is exactly condition (1) of the new criterion. For step 3 I checked the repeated-point case separately: `lem-sc-point-cartier` gives the Cartier ideal of $P$, `lem-sc-smooth-regular` and `lem-sc-regular-dim1-dvr` identify the local ring as a DVR, and `def-sc-divisor` makes $-2P$ the square of its maximal ideal. A section in $H^0(M(-P))\setminus H^0(M(-2P))$ has local coefficient in $\mathfrak m_P\setminus\mathfrak m_P^2$, so on a one-dimensional smooth curve every nonzero tangent vector detects it. This is condition (2). On $\mathbf P^1$, $\mathcal O(1)$ satisfies both drops even for $P=Q$ ($h^0=2,1,0$), while $\mathcal O$ satisfies the one-point drop but fails the two-point drop ($h^0=1,0,0$). These boundary cases agree with very ampleness of $\mathcal O(1)$ and failure for $\mathcal O$.

For step 4 I checked that the new node's statement, unlike the Lean `IsVeryAmple` type, specifically concludes that the morphism from the full section space is a closed immersion and pulls back $\mathcal O(1)$ to $M$. With $V=H^0(C,M)$ this is `def-sc-ample` word for word. I did not mark the criterion itself elementary; Stacks proves it using properness, finite fibres, cotangent-space surjectivity and a local algebra closed-immersion criterion. I removed no hypotheses and added only the divisor-module dependency missing from the item. The new node has only a statement, no disguised proof, and its `from.place` identifies the parent blueprint sentence it serves. In the repair review I checked the singleton closed-point counterexample, verified that (0) excludes it, and checked that item step 1 proves exactly (0) via nonzero evaluation at every closed point. The source record and this report record E7's addition of (0) to Stacks 0E8S.
