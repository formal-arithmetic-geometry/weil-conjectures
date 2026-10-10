# Stage-1 delivery: lem-sc-p1-serre-section-module-finite

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-p1-serre-section-module-finite.json`: item split in four steps. No new nodes; no Mathlib leaves.
- `citations.json`: verbatim statement excerpts for all step citations.

## Attachments

None. The source search found the sorry-bearing `ProjectiveLine.exists_exact_sigma_twist` in `WeilConjectures/AlgebraicGeometry/ProjectiveSpace/Duality.lean:83`, whose statement is the resolution, not this section-module finiteness claim. There is no declaration tagged with this item's blueprint id.

## WANTED

WANTED: Stacks Project `coherent.tex`, Lemma 0AG6 (coherent-lemma-coherent-on-proj) and Lemma 01YS (coherent-lemma-coherent-on-Pn), for lem-sc-p1-serre-section-module-finite. The `literature/stacks-project/` checkout is absent on this machine. I read the official Stacks pages online at `https://stacks.math.columbia.edu/tag/0AG6` and `https://stacks.math.columbia.edu/tag/01YS`; the proof origin is marked agent because the local source is absent.

## Corrections and limits

The imported node had no proof. Its statement is exactly the $A=k$, two-variable, $k=0$ instance of 0AG6(4), with no missing hypothesis. The proof in 0AG6 reduces to 01YS(5), whose argument gives the four steps here. No statement was changed. The existing three Mathlib search records cover the item; no new node was created. Whole-DAG and blueprint searches for `01YS`, `finite sum of twists`, and `graded section module` found no duplicate of a needed fact. All cited inputs are existing nodes.

## Review by C1

I checked Stacks 0AG6(4) and 01YS(5) against the item's statement. A field is Noetherian, $S=k[x_0,x_1]$ is generated in degree one, and $P=\operatorname{Proj}S$ is the standard projective line. Thus the finite generation in 0AG6 applies. The direct proof from 01YS avoids the closed-immersion reduction because $P$ is already projective space.

Step 1 uses the statement of `lem-pc-projective-space-twist-quotient`: it supplies both the finite sum of negative twists and a coherent kernel, under the Noetherian base hypothesis. `def-sc-p1-standard` identifies the Proj with $\mathbf P^1_k$. Step 2 uses `lem-sc-p1-twist-exists` for invertibility, `lem-sc-ext-tensor-exact` for exactness after twisting, `pqf-def-cohomology` for the long exact sequence, and `lem-pc-projective-space-serre-vanishing` for $H^1(\mathcal K(d))=0$ at high degree. Each of those facts appears in its cited statement; the resulting surjectivity follows from exactness. The maps are graded because the original quotient is a module map and multiplication on sections is functorial.

Step 3 uses the $H^0$ formula in `lem-pc-projective-space-twist-cohomology` to identify the section module of each $\mathcal O(-m_j)$ with the free shift $S(-m_j)$: for $d<m_j$ both graded pieces vanish, and for $d\ge m_j$ the monomials are a basis compatible with multiplying by $x_0,x_1$. It then applies the exact statement of `lem-sc-p1-graded-submodule-finite` to the high-degree graded submodule. A quotient of a finite module is finite, so Step 2 gives the high-degree conclusion. Step 4 uses the invertibility statement again and the local definition in `pqf-def-coherent` to check that each twist of $\mathcal G$ remains coherent; `lem-sc-p1-coherent-finite` states finite dimensionality of its $H^0$. Finitely many bases, together with generators in high degree, generate the full module.

I checked the edge cases $\mathcal G=0$, $\mathcal G=\mathcal O$, and $\mathcal G=\mathcal O(-1)$: their nonnegative section modules are respectively $0$, $S$, and $S(-1)$, all finite. The case $N=0$ makes the low-degree range empty. The quotient lemma's $m_j\ge0$ is used explicitly so the source section module is a direct sum of free shifts without stray negative pieces. The off-unit twist quotient, vanishing, and twist cohomology results are declared as generic tools in `split_report.tool_uses`. I found no hidden use of a cited node's proof, and no new assertion needing an uncited non-elementary result. The missing local Stacks checkout remains the only source limitation.
