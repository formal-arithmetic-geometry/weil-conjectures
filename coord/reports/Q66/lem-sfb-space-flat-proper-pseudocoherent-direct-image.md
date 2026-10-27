# Stage-1 report: lem-sfb-space-flat-proper-pseudocoherent-direct-image

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-flat-proper-pseudocoherent-direct-image.json`: split the unchanged statement in eight proof steps; no Mathlib match.
- `citations.json`: one verbatim statement quotation for every node used by every proof step (37 entries).
- `report.md`: this report. `searches.jsonl` is the unmodified output log of the required search command. `write_split.py` is sandbox-only preparation code.

New nodes: 0. New Mathlib leaves: 0. The required lemmas already exist, including the algebraic-space perfect-approximation theorem; they are cited rather than duplicated. Existing statement-only dependencies remain available for their own stage-1 workers.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id, pseudo-coherence and proper/flat direct-image terminology. No project declaration states this whole algebraic-space theorem and its projective-space clause. Scheme-only results and ring pseudo-coherence are not attachments. The item has no imported Lean declaration or Lean audit to repair.

## WANTED

None. The proof sources are present in the repository.

## Findings and corrections

The statement is unchanged, as are its statement dependencies, source, created record and imported blueprint ancestry. No statement dispute was found. The source's arbitrary-base-change assertion is outside this item's requested conclusion; the proof does not add or require it. I expanded the very short 0CTN proof through the approximation argument in 0CTL, specialized to the coefficient complex O_Y[0]. This avoids moving the item's conclusion into a new lemma.

I checked the current unit and chapter records, SETUP's three levels, GOAL, stages/1-dag.md, the worker brief, tools/README.md, and both copies of delivery-errors B--E. I read the newest blueprint under `literature/blueprint/latest/`, especially the ctf-stability unit and direct-images proof (3). The imported item is deep in that proof's coherent-duality prerequisite chain. Its inherited null blueprint ancestor is also what `tools/blueprint_refs.py ancestor` prints; I preserved it and its existing via chain. Searches of the whole imported blueprint for `flat proper pseudocoherent direct image`, `pseudo-coherent`, `0CTN`, `0A1P` and `projective space` found no blueprint theorem that duplicates this item. Generic comparison, homological-algebra and projective-space lemmas used outside this unit are declared in `split_report.tool_uses`; none changes the unit's direct-image route.

The main repairs during self-review were to use the actual statement of the etale-chart calculus for unbounded base change, to include a single K-injective representative when converting derived local models to the definition's chain-map formulation, and to cite the polynomial-Proj/base-change-projective-space comparison rather than silently identify two interfaces. I replaced an informal quasi-separatedness argument for projective space by the existing qcqs-over-affine and qcqs-morphism-permanence statements.

## Unfinished work

None for this one-level stage-1 split. No Lean was written and no compiler, Lake or build command was run. All authored files are in the authorized sandbox; the shared repository and launcher files were only read.

## Not duplicates

No new nodes were created. The existing scheme theorem `lem-sfb-flat-proper-pseudocoherent-direct-image` is not the algebraic-space theorem: the source need not be a scheme after an affine etale base change on the target. Its existence is therefore not grounds for an attachment or a one-line scheme reduction. The existing `lem-sfb-proper-support-tensor-perfect` handles perfect inputs, and `lem-sfb-space-pseudocoherent-perfect-approximation` supplies the approximation of a pseudo-coherent input; neither individually restates the item.

## Review by Q66

I read Stacks `spaces-perfect.tex` at 0CTN (flat proper pseudo-coherent direct image), the full proof of 0CTL (pseudo-coherent tensor direct image), and the statement and proof setup of 0A1P (perfect tensor direct image). I checked 08FA's unbounded upper bound, 08HP with the approximation definitions 08HI/08HJ, and the 08HE etale descent comparison. For the specialization I read `constructions.tex` 01NF/01NG and the paragraph identifying projective space with relative Proj using 01O3. For the representative issue I read `sites-cohomology.tex` 0D6G and `derived.tex` 070I, and the statements of the existing K-injective resolution and slice-restriction nodes. There are no new-node sources to audit.

1. Step 1 uses the fibre-product/covering theorem for the base-changed etale charts, the flat/proper/fp locality theorem for preservation of all three hypotheses, the fp-qcqs-source theorem over an affine scheme, the space pseudo-coherence definition for restriction of models, and the derived-etale-chart-calculus theorem for the exact slice base-change isomorphism. I opened each of these node statements. In particular the chart-calculus statement gives base change for every unbounded complex; no bounded-below or arbitrary nonflat base-change claim is substituted. Quasi-compactness of the original target is never assumed.

2. Step 2 uses exactly the upper-bound and space perfect-approximation statements. The former requires a qcqs morphism and a quasi-compact target; the latter requires an absolutely qcqs source. Step 1 supplies these. The approximation statement explicitly gives the triangle in D_QCoh, so there is no unproved quasi-coherence assertion about its cone. The long-exact-sequence node supplies the cone calculation. At degree a the surjection in degree a and injection in degree a+1 are both used.

3. Step 3 uses the perfect tensor-image theorem with a bounded coefficient complex; it is not used for a merely pseudo-coherent input. I checked every coefficient hypothesis: O_Y has a finite presentation and is quasi-coherent, flatness of atlas stalks follows from the local-property chart test and the flat-morphism definition, and the module-flat-chart-test statement identifies these with the geometric-stalk condition required by the tensor-image theorem. This test applies because the reduced target is a scheme. The support of O_Y is Y with zero annihilator; zero terms have empty support, covered by the proper-support-closed-operations statement, including its empty-family clause. The tensor unit identification is written termwise on a K-flat representative, rather than cited from an unrelated definition.

4. Step 4 uses the same upper-bound statement on C with b=a-1, the derived-module-calculus definition for the actual additive K-injective-derived direct image, the right-derived-triangulated theorem, and the long-exact-sequence theorem. I checked the latter two statements and read the corresponding right-derived-functor Lean source without compiling. The arithmetic is a=m-N-1 and b+N=m-2. Thus both adjacent cone groups vanish for i at least m. This is an elementary application of the cited statements, not an assertion that Rg_* is t-exact. It needs no lower bound on C.

5. Step 5 uses the qcqs-pushforward theorem only for preservation of quasi-coherent cohomology, the derived etale--Zariski equivalence for its quasi-inverse and exact pullback, the etale pseudo-coherence-descent theorem for each fixed m, and the scheme pseudo-coherence definition's all-m characterization. I opened all four statements. Perfection of the approximating pushforward means exactly local strictly perfect models in the tensor-image theorem's statement, so those maps satisfy the descent theorem's required approximation inequalities. I do not claim that one strict perfect model works for every m. The scheme all-m characterization supplies bounded-above finite-free models after all m have been established.

6. Step 6 uses the space definition's actual quasi-isomorphism condition, existence of K-injective resolutions on a small ringed site, preservation of K-injectivity under slice restriction, the Hom_K-to-Hom_D bijection into a K-injective complex, and exact slice restriction from the chart-calculus node. These are the precise contents of the opened statements. A derived isomorphism from a bounded-above model therefore becomes a chain-map quasi-isomorphism into the restriction of one global I. Pulling the covers back to any other etale object provides the required covering sieve. No global bounded-above representative or uniform bound is assumed.

7. Step 7 uses the free-projective-bundle/base-change-space comparison for the polynomial Proj convention, the cartesian projective-space-base-change theorem, properness of projective space over every scheme, the standard-chart theorem for the cover and polynomial rings, polynomial-projection flatness, locality of flatness for etale scheme covers, and the local-finite-presentation definition. I read each statement: the standard-chart node includes the base ring maps, and polynomial-projection flatness permits arbitrary rings. The finite-presentation calculation has n generators and zero relations. The Proj comparison is used only on scheme bases Spec A and V; it is not incorrectly applied directly to an algebraic-space base.

8. Step 8 uses qcqs-over-affine and qcqs-morphism-permanence to obtain finite presentation of the proper, locally finitely presented scheme projection. Its final comparison uses exactly the etale-chart-calculus statement again. Steps 1--6 can then be applied to each scheme chart, so no separate unsupported theorem about projective projections over arbitrary spaces is needed. The local-model assembly is the already written step 6.

I tested empty spaces and the zero complex: the covering and approximation arguments are vacuous or give zero models, and the empty-support clause is explicit. For n=0 the one standard chart is Spec R, with zero polynomial variables, giving the identity projection. The zero ring gives an empty chart and poses no problem. Non-Noetherian rings are allowed by every cited theorem. The only degree bounds are the local upper bounds in the source approximation and the uniform direct-image bound after affine reduction. None imposes the forbidden lower cohomological bound.

Against delivery-errors B--E: there are no new statements, hollow definitions or unsupported Mathlib leaves; every step citation is to an existing statement read in full and quoted verbatim in citations.json; every non-elementary input is named; no proof is borrowed from a cited node's internal construction. The written argument supplies the cone, degree calculation, tensor unit and projective chart calculation rather than relabelling the conclusion. Every step is below 2000 characters, and I checked that none hides a new comparison lemma beyond the comparisons explicitly cited. No SGA source is used. Mathlib searches were actually run through msearch.py in all four kinds, with a second semantic phrasing; their log is retained and their query texts are copied exactly. Returned hits concern ordinary pushforward or scheme morphism properties, not this derived algebraic-space assertion.
