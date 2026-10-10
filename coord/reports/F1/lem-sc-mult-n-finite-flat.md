# Stage 1 report: lem-sc-mult-n-finite-flat

## Files written

- `dag/nodes/sec-abelian-varieties/lem-sc-mult-n-finite-flat.json`: item split into two source-based proof steps; no new nodes.
- `citations.json`: citation for the existing finite-kernel node used in step 1.

## Attachments

None. The source declarations `AlgebraicGeometry.isFinite_npow_id`, `AlgebraicGeometry.finrank_npow_id`, and `AlgebraicGeometry.finrankΓ_torsionSubgroupScheme` are not exact statements of the item, and their audit is transitively dependent on sorry declarations, so they are not attachments.

## WANTED

None. The Stacks sources cited by the imported item are present in the project literature references.

## Not duplicates

The first worker created no nodes. In the second reading one general input was added.

- `lem-sc-positive-ample-hilbert-degree` vs `lem-sc-isogeny-facts`: both cite Tag 0BEV, but the former states positivity of the Hilbert degree of an ample module on any nonempty proper scheme, whereas the latter states multiplication-isogeny and torsion conclusions only for abelian varieties over algebraically closed fields; its proof uses Tag 0BEV without stating the positivity fact.

## Review by F1

I read the item source `literature/blueprint/master/blueprint/sec-abelian-varieties/sk-prop-av-isogeny/lem-sc-mult-n-finite-flat.md` and the imported statement. Its blueprint proof explicitly records Stacks Groupoid Schemes Lemma 39.9.8 (Tag 0BFG) and Proposition 39.9.11 (Tag 03RP) as the classical input, with no intermediate lemma. I also read `lem-sc-mult-n-finite-kernel.json`; its statement supplies exactly the finiteness of `[n]` and of `A[n]`, which is quoted verbatim in `citations.json` and used in step 1. Step 2 checks the remaining conclusions directly against the two cited Stacks results: finite locally free degree `d^(2g)` gives flatness and rank, while Proposition 39.9.11 gives the finite flat kernel and its order; this is the item's recorded source input and is marked elementary in the DAG sense of an imported theorem interface with no proof requested. The hypotheses `A` abelian of dimension `g` over a field and `d >= 1` are the hypotheses of the item and of the recorded Stacks input. I tested the edge case `d = 1`: the statement gives the identity map, rank one, and a kernel of order one, as expected. I searched Mathlib with LeanFinder, Loogle, grep, and LeanSearch (the latter was unavailable); the hits were only generic smoothness/module facts or unrelated cyclic-group results, so no Mathlib leaf applies. I did not create clause nodes because they would merely restate the finite-flat/rank/order clauses of the item itself.

## What was wrong or incomplete

The imported node had an empty proof despite its blueprint source explicitly naming the Stacks input. Its `blueprint.from` and `same_as` fields were also unset; these are now filled. The existing Lean declarations are component statements rather than an exact match for the item and are transitively sorry-dependent, so attaching them would be incorrect.

## What could not be finished

Nothing.

## Second reading by F1

- Item statement: checked against Stacks Groupoid Schemes Lemma 39.9.8 (Tag 0BFG, `lemma-degree-multiplication-by-d`) and Proposition 39.9.11 (Tag 03RP), parts (3) and (5): arbitrary field, abelian variety of dimension $g$, and $d\geq1$ agree clause by clause. For $d=1$, $[1]$ is the identity with rank and kernel order one; for a dimension-zero abelian variety the formula also gives one. The unit point excludes an empty abelian variety.
- Step 1: `lem-sc-mult-n-isogeny` states surjectivity and finite kernel under precisely these hypotheses; `def-sc-isogeny` turns these into an isogeny. Verdict: valid.
- Step 2: `lem-sc-isogeny-degree` states finite flatness, locally free rank equal to the kernel order, and equality with finite-morphism degree. Verdict: valid for the isogeny of step 1.
- Step 3: `lem-sc-abelian-variety-projective`, `lem-sc-ample-tensor`, and `lem-sc-mult-n-pullback` give an ample symmetric $\mathcal N$ and $[d]^*\mathcal N\cong\mathcal N^{\otimes d^2}$, exactly as in the first paragraph of Tag 0BFG. Verdict: valid.
- Step 4: `lem-sc-hilbert-polynomial` and `def-sc-hilbert-degree` give the degree-$g$ coefficient. Substitution $m\mapsto d^2m$ multiplies that coefficient by $d^{2g}$, including $g=0$. Verdict: elementary calculation is explicit.
- Step 5: `lem-sc-abelian-variety-characterization` supplies integrality, `lem-sc-deg-pullback-finite` the finite surjective pullback equation, and `lem-sc-positive-ample-hilbert-degree` the strictly positive factor to cancel. The finite-morphism degree equals the kernel order by step 2. Verdict: valid for arbitrary $k$; agrees with the final paragraph of Tag 0BFG.
- New node `lem-sc-positive-ample-hilbert-degree`: checked against Stacks Varieties Lemma 33.45.9 (Tag 0BEV, `lemma-ample-positive`) and Definition `definition-intersection-number`; diagonal specialization of its intersection polynomial is the Hilbert degree. The statement is self-contained, has definition dependencies, is TeX once, has no proof, and records actual LeanFinder, Loogle, grep, and unavailable LeanSearch results. Searches of the blueprint and existing nodes found only a curve-specific degree lemma, not this general result. A point has degree its positive length; the empty scheme is excluded; the assertion is independent of $d$.
- Changed: replaced the uncited Stacks conclusion in the old step 2 with the source's five-step proof, added the necessary general positivity input, updated `proof_deps` and all verbatim citation quotes, and recorded the exact source labels. The repository's regenerated Stacks `.tex` and blueprint files are absent on this clone, so I checked the official Stacks tag pages and the upstream `varieties.tex` label instead.
