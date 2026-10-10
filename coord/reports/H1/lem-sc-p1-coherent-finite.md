# Stage 1 report

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-p1-coherent-finite.json`: split item; no new nodes.
- `citations.json`: verbatim citations for both proof steps.

## Attachments

None. `AlgebraicGeometry.ProjectiveLine.finiteDimensional_H` has no literal `sorry`, but its proof reaches the sorry-backed `finite_sections_higherDirectImage`; the item audit therefore remains `rests_on_sorry`.

## WANTED

None.

## Review by H1

I read the imported blueprint proof and the project source `WeilConjectures/AlgebraicGeometry/Cohomology/ProjectiveLine.lean`, including the declaration `ProjectiveLine.finiteDimensional_H` and its direct-image dependencies. The declaration has the right finiteness conclusion parametrized by `q ≤ 1`, but its transitive proof uses the sorry-backed direct-image finiteness theorem, so I did not attach it. I also read `lem-pc-coherent-hi.json`: its statement explicitly gives finite `A`-modules for cohomology over a proper morphism to `Spec(A)` with `A` Noetherian. Step 1 checks that the Proj presentation in `def-sc-p1-standard` makes the structure map of `P^1_k` projective, and `lem-pc-projective-proper` says projective morphisms are proper; the field is Noetherian and coherence supplies the required quasi-coherent finite-presentation module. Step 2 specializes the finite-module clause to `A = k`, then uses the elementary fact that a finite module over a field is finite-dimensional, for `i = 0,1`. Every citation in `citations.json` is copied verbatim from the cited node statement. I removed the imported Cech claims because they were not needed for this route and their kernel/cokernel finiteness argument was incomplete for `H^0`.

## What was wrong or incomplete

The imported second paragraph invoked a structure theorem and torsion argument without citing a node and did not establish all hypotheses. The replacement follows the existing coherent-finiteness node and records all proof dependencies.

## Second reading by H1

- Item statement: checked against Stacks Cohomology tags 02O5 and 02O6 and the imported projective-line blueprint; the field, coherent sheaf, and conclusions for $H^0$ and $H^1$ agree hypothesis by hypothesis.
- Step 1: checked [def-sc-p1-standard] for the Proj presentation, [def-pc-projective-morphism] for the projective convention, [lem-pc-projective-proper] for properness, and [lem-pc-coherent-hi] for its direct coherent-sheaf hypothesis; corrected the inaccurate finite-presentation wording.
- Step 2: checked [lem-pc-coherent-hi] supplies finite $k$-modules over $\operatorname{Spec}k$ and that finite generation over a field is finite-dimensionality; the $i=0,1$ specialization is direct.
- New nodes: none; no new statement required a B1--B7 audit or duplicate search.
- Edge cases: the argument remains valid for the zero coherent sheaf, any field (including finite fields), and $i=0,1$; no empty-scheme or $n=0$ hypothesis is introduced.
- Changed the step-1 text and dependency list to cite [def-pc-projective-morphism] and state the actual coherent-sheaf hypothesis of [lem-pc-coherent-hi].
- Added the corresponding verbatim citation and this second-reading record; no source statement or target conclusion was changed.
