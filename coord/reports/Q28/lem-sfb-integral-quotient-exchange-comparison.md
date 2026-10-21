## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-quotient-exchange-comparison.json`: statement unchanged; seven-step split; Mathlib verdict no match for the entire normalized internal-module assertion.
- `citations.json`: one literal statement quotation for each of the 21 step/node citations.
- `report.md`: this report. `searches.jsonl` contains the real search-command records; `write_split.py` is the sandbox-local reproducible JSON writer, not a delivery node.

There are **0 new nodes and 0 new Mathlib leaves**. The sandbox initially contained no node, proof, report or search log. The current repository node was retained with its original statement, source, created/blueprint metadata and original searches, and the searches run here were appended.

## Attachments

None. Searched the actual `lean/WeilConjectures` library for the item tag and integral/quotient reduction/exchange notions, and inspected the generic exchange API. No project declaration gives the full internal-module assertion and independently normalized ringed realization. The existing ringed theorem `AlgebraicGeometry.Scheme.finiteReductionExchange_rectangle` in `lean/Sheaf/Paper/FiniteReductionExchangeRectangle.lean` was read, but it is not a declaration under `WeilConjectures/` and does not supply the internal/section identification asserted here. Its existing DAG node is reused, without claiming a finished attachment.

## WANTED

None. All sources used are present in the read repository.

## Corrections and scope

The seed had no proof. Its statement is correct and unchanged. The missing work was not an existence statement about some comparison: it was coherence of the specified balancing maps and preservation of the independently chosen derived adjunctions.

The old Poincare comparison `lem-pd-module-ringed-topos-derived-comparison` assumes separated schemes of finite type over a positive-characteristic field. I did not apply it to the arbitrary schemes here. Instead I use the existing unrestricted `lem-pd-section-derived-pushpull-normalization`, whose statement explicitly includes the independently derived units, counits and geometric composition maps. Scalar normalization is the separate unrestricted `lem-sfb-internal-section-scalar-adjunction`, and flat/K-flat preservation is `lem-pe-internal-section-tensor-comparison`.

The intrinsic rectangle statement points to `def-weil-pbc-four-corners` for its projection adjuncts, but the explicit formula is actually in `def-weil-pbc-four-arrows`. Step 6 cites that definition directly for the normalization formula. The four-arrow applications also assume properness, completeness and finite-origin witnesses. Those assumptions are not imported: Step 6 compares its displayed definitions, while Steps 3-5 independently prove the equality for arbitrary K and arbitrary scheme morphisms using the unrestricted mate cube. No four-arrow invertibility assertion or finite-origin theorem is applied. In particular this proof does not infer equality of quotient-linear maps by forgetting their quotient action; scalar restriction is not generally faithful on derived morphisms.

The proof follows the proper-image unit's paragraph (3), canonical reduction of exchange, and supplies its omitted coefficient/mate calculation. It does not change the unit route or target statements. Generic off-unit tools are declared in `split_report.tool_uses` for the maintainer to judge; no top-level `tool_uses` was added.

## Unfinished work

None for this stage-1 item. The cited nodes retain their own stage states. No Lean was written, no compiler or build was run, and no repository or launcher file was modified.

## Not duplicates

No new nodes. Whole-DAG tag and concept searches and whole-blueprint searches (`exchange`, `scalar.*pullback`, `coefficient.*square`, `internal`, `finite-exchange`, `reduction`) led to reuse of the existing mate cube, scalar adjunction comparison, derived section normalization and finite rectangle. No imported blueprint statement has the full assertion with these internal-module and normalization clauses, so `blueprint.same_as` remains empty. The existing generic ringed rectangle is a dependency, not a new relabelling of the item.

## Mathlib searches

Ran the required launcher search command with LeanFinder, LeanSearch, Loogle and grep, with two distinct natural-language phrasings. Read the hits. LeanFinder found underived `SheafOfModules.pullbackPushforwardAdjunction` and related formulas. LeanSearch found `SheafOfModules.pullbackComp`, its conjugate identity, and the ordinary `ModuleCat` scalar pseudofunctor. Loogle found `CategoryTheory.mateEquiv_vcomp`, `mateEquiv_hcomp` and conjugate variants; their source in `Mathlib/CategoryTheory/Adjunction/Mates.lean` was read. The sheaf pullback source in `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean` was also read. These are ingredients, not one-line specializations proving the actual unbounded quotient-module realization. The recorded CategoryTheory grep found no coefficient-exchange assertion. No service failure was recorded as a negative result. The initial asynchronous LeanFinder call's completed log was reused; its query was repeated once to recover and read the full printed signatures.

## Review by Q28

I read the current chapter and proper-image unit, all of the integral detail proof in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-integral.proof.md`, and Stacks `sites-cohomology.tex` Remark 07A7, Remark 0E47 (`remark-compose-base-change-horizontal`) and Remark 0E48 (`remark-compatible-with-diagram`). Stacks says the compatibility verification is omitted; the split supplies it through the existing explicit mate-cube theorem. I also read the section-module realization and scalar comparison nodes and the concrete finite rectangle Lean source to verify orientation. There are no new-node sources to review.

For Step 1 I checked the statements, not merely the proofs, of `lem-pd-section-derived-pushpull-normalization`, `lem-sfb-internal-section-scalar-adjunction`, `lem-pe-internal-section-tensor-comparison`, and the ambient exchange definition. They respectively give the actual derived adjunction and composition normalization, the actual derived scalar comparison on balanced generators, K-flat preservation, and the exact unit--square--counit formula. Their arbitrary-scheme and unbounded hypotheses match the item. This replaces the tempting but invalid use of the restricted Poincare statement.

For Step 2 the profinite inverse-image statement explicitly includes compatibility with the finite projections and compositions; the integral-limit node identifies the actual coefficient sheaf with that tower. The uniqueness check against every projection ensures that it is the coefficient identification in the prescribed lambda comparison. No claim that arbitrary inverse image preserves arbitrary limits is used.

For Step 3 I checked each domain and target of the displayed inverse-image cube. The K-flat resolution node supplies flat-term representatives, the ringed tensor/pullback node preserves them along geometric edges, the change-of-rings node computes quotient scalar extension, and the derived compositor node specifies its value on these representatives. The short exact-tensor test written in the step proves that scalar extension also preserves this class; it does not assume S is flat over R. On these models both paths send the same local balanced tensor to the same pullback tensor, with its S-action. This is an elementary comparison of the cited canonical formulas, not a new auxiliary lemma hidden behind the word 'coherent'.

For Step 4 I compared the exact defining adjunct of rho in the direct-image comparison statement with the mate definition. They agree in the displayed orientation, giving the counit identity. The ambient exchange definition gives the other two mates. In Step 5 I checked the generic mate cube's four adjunctions and all four connecting functors against Step 3. With its comparisons p_u=lambda_u^{-1}, its comparison mates are rho, not their inverses. The displayed intermediate equality has source D_{Y'}L_{g,R}F_{f,R}K and target F_{f',S}L_{h,S}D_XK. Precomposition by lambda_g and postcomposition by F_{f',S}(lambda_h) gives the exact source and target stated in the item.

For Step 6 I read the statement of the intrinsic finite rectangle and the explicit chi and finite-projection definitions in `def-weil-pbc-four-arrows`. The balanced representative formulas give chi=lambda; their counit-adjunct formulas give projection=rho. The ringed exchanges are the independently specified ones by Step 1. Consequently the rectangle with F(lambda_h^{-1}) on its right is precisely the same equation before the cancellation of Step 5. This is an identification of specified arrows. I have used only the definition formulas of the four-arrow presentation here, not its properness-dependent finite-exchange isomorphism.

For Step 7 the direct-image comparison statement asserts the requisite lambda and rho natural isomorphisms for all unbounded inputs. Functors preserve those inverses. Equality is already an equality of natural transformations, so naturality in K is preserved without making functorial choices of representative complexes.

I tested the argument at K=0, at n=1, for identity squares, for a zero/empty corner, and for unbounded K with no completeness condition. In an identity square all mate formulas reduce to the same identity under canonical comparators; for K=0 and an empty corner both paths are the unique zero morphism. The K-flat argument handles unbounded complexes with direct-sum total tensor, never an unjustified bounded resolution. No exchange inverse is used. The comparison retains the finite coefficient action at every step. All seven steps are under 2000 characters; none hides a separate non-elementary subclaim without a cited node.

I checked delivery-errors B1-B10 (no new nodes, genuine searches, preserved blueprint fields and no attachment overclaim), C1-C8 (all non-elementary ingredients cited with verbatim statement quotations, no restricted hypothesis substituted, generic tools declared), D1-D5 (the steps carry the balancing and mate argument, no new restatement lemma), and E1-E7 (typed objects and all hypotheses as above). The server-only preliminary `check_dag` and `review_split` passed. The required final dry run and direct push follow this review.
