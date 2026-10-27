# N6 stage-1 direct delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-projective-cohomology-coefficient-kunneth.json`: existing statement split into ten steps, statement and statement dependencies unchanged. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every dependency of every proof step.
- `report.md`: this report. `searches.jsonl` retains the actual exploratory searches made in this sandbox.

## Attachments

None. Searching the live `lean/WeilConjectures/` by the exact blueprint tag and the coherent/projective/Kunneth notions found no declaration proving all clauses of the item. `DerivedCategory.exists_quasiIso_of_zero_differential_of_projective` in `WeilConjectures/CategoryTheory/DerivedCategory/Perfect.lean:488` does prove the elementary splitting used in Step 3, but does not state this item. Its cycle-section argument is written out directly rather than introducing another node. The existing bounded-free splitting node requires a bounded finite-free representative, which is not initially given for these derived sections.

## WANTED

None. The necessary Stacks sources are available locally. No SGA source is used.

## Findings and corrections

There was no earlier sandbox split or report to recover. The live item's statement is valid as written; there is no statement dispute and no alteration of its hypotheses. Its existing Mathlib searches, including both semantic phrasings, were retained and the recorded hits read. Those hits concern condensed categories, group cohomology, cotangent cohomology and ordinary scheme pullback, not this coherent coefficient theorem.

The whole-DAG tag search found the existing `lem-sfb-flat-space-derived-external-cup`, which supplies a derived isomorphism and its full structure compatibilities. It is reused, not recreated. Likewise `lem-sfb-space-affine-derived-projection-formula` already supplies the coefficient projection arrow for arbitrary modules. A prospective general derived cup-coherence node was searched but not created: the existing external-cup statement already contains all the structure-coefficient coherence needed here. Exploratory Mathlib searches found `CategoryTheory.Adjunction.rightAdjointLaxMonoidal`, whose tensor-of-counits formula was read at Mathlib/CategoryTheory/Monoidal/Functor.lean:947; this abstract result alone does not state the geometric theorem, and no new node or leaf is claimed for it. An initially invalid short Loogle identifier was followed by the full valid declaration-name search; the log records both honestly.

The item's inherited blueprint ancestry has `from.node: null`; `tools/blueprint_refs.py ancestor` returns `None`. I preserved that inherited ancestry and its explicit place/via chain, filled `same_as` after searching the imported blueprint, and described the current-latest direct-images proof (3) in `split_report.blueprint`. The current latest blueprint's direct-images argument uses proper images, open immersions and compactification. This coherent calculation is a supporting tool deep in the alteration/Picard prerequisite chain; it does not change that route. The stored unit record points to the older six-functors chapter while the inherited item chapter is six-functors-basics; neither maintainer-owned field was changed.

## Unfinished work

None for this one-level split. The cited existing unsplit nodes remain their own items; no claim of a finished Lean proof is made. Delivery validation is recorded below after running the required server dry run.

## Not duplicates

No new nodes. In particular, no extra node restates the external-cup or coefficient clauses. The derived external-cup theorem is a distinct existing, more general derived statement; this item's steps prove its cohomology consequences under finite-projectivity and derive arbitrary coefficients by the projection formula. The finite-free bounded-complex splitting was not duplicated: the short lifting argument is a step of the proof.

## Review by N6

I read the item's Stacks sources `spaces-perfect.tex`, Tags 08IN (lemma-cohomology-base-change) and 08IR (lemma-compare-base-change), including their canonical adjunction-mate maps. I also read the cup diagrams in `sites-cohomology.tex`, Tags 0FPL, 0FPM, 0FPN and 0H9A. These apply to structure modules on ringed etale sites; none replaces them by constant finite coefficients. For the algebra I read the projective lifting criterion in algebra.tex (05CF), flat composition (00HC), flat localization (00HT), and the K-flat definition/computation and bounded-above-flat argument in more-algebra.tex/sites-cohomology.tex. Every cited node's statement was opened; the quotes in citations.json are the statements actually used, not their proofs. There are no new-node sources to check.

Step 1 uses `lem-sfb-space-quasicompact-fppf-local` for arbitrary algebraic-space base change of quasi-compactness, `lem-sfb-space-flat-proper-fp-locality` for its separate flatness clause (without assuming properness or finite presentation), and `lem-weil-pbc-flat-ring-map-comp` on etale charts. The elementary diagonal factorization and inverse-image test prove the composition and quasi-separatedness facts in the step itself; no unprovided space-permanence claim is taken from a scheme-only node. Thus the projection formula later applies to P as well as to X,Y.

Step 2 uses `lem-sfb-ringed-site-global-module-abelian-cohomology` for the exact underlying-additive cohomology convention and scalar action. `lem-sfb-flat-space-derived-external-cup` says precisely that the canonical external cup is an isomorphism in D(R), with products, units, all relevant pullbacks and scalar-base-change compatibility. I checked its flat qcqs hypotheses against Step 1 and its dependencies for a path back to this item; its statement dependencies are definitions, not this coefficient theorem. The proof does not infer a degreewise tensor formula from an isomorphism without the intervening algebra.

Step 3 uses the actual lifting clause of `def-weil-pbc-projective-module` to split Z^i -> H^i and the quasi-isomorphism/localization clause of `def-weil-abstract-derived-category`. The explicit chain map induces identity on cohomology and is therefore a quasi-isomorphism. Finitely many nonzero cohomology modules make its source bounded. This is a short construction, so I kept it elementary rather than creating a formality node. Crucially the section choices do not define alpha or kappa, nor are they asserted natural.

Step 4 uses `lem-weil-pbc-projective-module-flat` and `lem-pc-module-bounded-flat-kflat` exactly on these bounded zero-differential complexes. `lem-pc-source-kflat-module-tensor-model` allows an arbitrary second complex. The canonical pairing in `def-sfb-ringed-site-module-cup-product` is the class of the tensor of cycles, so the calculated cohomology isomorphism is the canonical edge map. Tensoring the finite-free retractions explicitly proves projectivity of the product cohomology; no generic Kunneth theorem with a hidden field or flat-coefficient hypothesis is used.

Step 5 uses the full statement of `lem-sfb-space-affine-derived-projection-formula` with E=O_Z, for each of the three flat qcqs spaces and an entirely arbitrary R-module N. That statement includes exactness of N -> O_Z tensor_R N, ordinary representation of its derived pullback, and naturality in N. Hence neither properness, a Noetherian base nor flatness of N is being supplied tacitly.

Step 6 uses the same module K-flat tensor computation for the now-projective cohomology of each Z, and `lem-sfb-ringed-projection-tensor-composition` for the canonical projection arrow's naturality and unit normalization. The tensor-of-counits definition in `def-sfb-ringed-site-module-cup-product` identifies its value on a tensor a tensor n with the cohomology map induced by O_Z -> N_Z, 1 -> 1 tensor n: the extra unit/counit cancels by the triangle identity. Thus the calculation proves invertibility of the specified alpha, rather than inventing an isomorphism after choosing sections.

Step 7 writes kappa_N as (kappa_R tensor identity) followed by alpha_P,N and checks it on each pure tensor using the same cup definition. Tensoring a known isomorphism requires no flatness; its inverse tensors to the inverse. This is the substantive coefficient assembly in the item, not an invocation of another node restating its coefficient clause.

Step 8 uses `lem-weil-pbc-mate-pasting` for identity/composition of the canonical adjunction-induced pullbacks and the existing derived external-cup theorem for their product and unit preservation on O-coefficients. Coefficient naturality is verified using the commuting local formula a -> t-sharp(a) tensor n and the formula proved in Step 6. It uses naturality of the adjunction unit, not exactness of a possibly nonflat module pullback. The maps for kappa_N then agree by the factorization already proved.

Step 9 uses the derived external-cup theorem's arbitrary-ring base-change map, and `lem-weil-pbc-localization-flat` with the multiplicative set generated by s. Flatness preserves kernels, images and quotients, so the cohomology/base-change identification follows. I checked the actual section 1 tensor n maps to 1 tensor (1 tensor n), so the localized coefficient square is the asserted one. Finite-free retractions remain retractions after localization, ensuring the localized spaces still satisfy the cohomological hypotheses.

Step 10 uses the external-cup theorem's commutative derived algebra structures and `lem-sf-ringed-derived-closed-symmetric-monoidal` for the exact Koszul symmetry (-1)^(ij). The cup definition supplies bilinearity. The single interchange of b and c proves the exact source multiplication sign (-1)^(deg(b)deg(c)); it is not inferred from an unsigned tensor algebra convention.

I tested the edge cases X=T and Y=T (the maps reduce to the projection/identity coefficient map), empty factors and the zero ring (all relevant modules are zero), N=0, nonflat N=R/I, vanishing of all positive cohomology, degree zero, odd degrees over characteristic two, s=1 and s=0. The zero-differential K-flat computation handles R/I without a Tor term because the cohomology modules, not N, are projective. The product cohomology bound is the sum of the two original bounds. No hypothesis was inserted to eliminate a Tor obstruction.

Against delivery-errors B--E: the JSON retains normal single-escaped TeX and all inherited metadata; no unsplit new node contains a proof; all notions in the unchanged statement have their existing definition dependencies. Every non-elementary input is a cited node whose statement supplies it. The few-line cycle-section, finite-retraction, coefficient-generator and sign calculations stay as elementary steps. There is no circular dependency, no clause moved into a fresh node and no claim that an objectwise isomorphism proves naturality. All steps are under 2000 characters, so no long-step lemma is hidden. Generic off-unit proof tools are declared in split_report.tool_uses; no maintainer-owned tool_uses or reviewed field was set.

## Validation

First server dry run rejected the phrase “the item's hypotheses” in Step 3 as non-self-contained. Replaced it with the explicit condition that the cohomology modules of C are finite projective. The statement and argument are unchanged. Final server dry run passed: `OK (not pushed) deliver/N6/lem-sfb-projective-cohomology-coefficient-kunneth at 8fc8f99c2b9: preflight passed`. The required delivery tool ran server preflight, including DAG and split checks. No checks were run locally and no Lean compiler was invoked.
