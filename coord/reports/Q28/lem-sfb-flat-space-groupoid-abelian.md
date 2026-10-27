# Stage-1 report: lem-sfb-flat-space-groupoid-abelian

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-space-groupoid-abelian.json`: statement; split by direct application of the existing stronger same-unit node `lem-sfb-flat-space-groupoid-kernels-cokernels`. Statement and statement dependencies retained. Mathlib verdict: no match.
- `citations.json`: the single proof citation with its verbatim statement excerpt.
- `searches.jsonl`: five searches run through the mandated msearch command, with both semantic phrasings, Loogle, LeanSearch and grep. All five services/commands answered successfully.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean files written or compiler/build commands run.

## Attachments

None. Searches of `lean/WeilConjectures/` by the exact blueprint tag and by groupoid/module/abelian concepts found no declaration proving this item. The related `AlgebraicGeometry.Scheme.groupoidModule_limits_colimits` in `lean/Sheaf/AlgebraicGeometry/GroupoidModuleLimitsColimits.lean` is scheme-only and its proof is `sorry`; it is not an attachment for algebraic spaces.

## WANTED

None. The required source is present as `literature/stacks-project/spaces-groupoids.tex`.

## Findings and corrections

The imported item has no proof. The DAG already contains `lem-sfb-flat-space-groupoid-kernels-cokernels`, created by Q23 for `lem-sfb-stack-smooth-qcoh-exact`, before this work. Its statement includes every conclusion here and, additionally, faithfulness and reflection of isomorphisms. It was unsplit with empty proof dependencies when read. I reused it rather than making another node or duplicating its future split. The new proof explicitly matches its objects, morphisms, pullback direction, cocycle convention and hypotheses, then takes precisely its abelianity and underlying kernel/cokernel conclusions. The existing theorem is a dependency, not a claim that its own proof has been finished.

No statement dispute was found. No hypothesis, conclusion or coefficient category was changed. The existing `blueprint.from.node = null` is inherited; `blueprint_refs.py ancestor` also returns None. Its descriptive place is already specific and was preserved. The current blueprint's direct-images proof (3) is read from `literature/blueprint/latest/`, and this auxiliary prerequisite remains in the inherited unit route; both item and cited node have unit `sk-thm-sf-ctf-stability`.

## Not duplicates

No new node was created. The item is a consequence of the existing `lem-sfb-flat-space-groupoid-kernels-cokernels`; its stronger statement covers this item. A future maintainer consolidation could merge the two ids, but this delivery changes only its assigned item.

Searches before writing: whole-DAG tag search for 06VZ and groupoid/abelian/kernel/cokernel concepts; `blueprint_refs.py search 'groupoid'`, `'06VZ'`, and `'quasi-coherent modules'`; project Lean exact-tag and concept searches. The blueprint hits concern scheme descent, ordinary quasi-coherence or unrelated group varieties, rather than this flat algebraic-space groupoid theorem; `same_as` remains empty.

## Mathlib searches

I read all five msearch outputs recorded in searches.jsonl. LeanSearch returns ambient `SheafOfModules.instAbelian`, `ModuleCat.abelian`, `Action.instAbelian`, presheaf, scheme-module, finitely generated module and condensed-module instances. The first LeanFinder phrasing similarly returns ambient module-sheaf instances and quasi-coherent presentation data; the second returns flat scheme morphism facts, ideal-sheaf kernels and quasi-coherent presentation data. Loogle and the targeted grep return zero hits. I read the ambient sheaf abelian instance in `Mathlib/Algebra/Category/ModuleCat/Sheaf/Abelian.lean`, the presentation-based quasi-coherence definition in `Sheaf/Quasicoherent.lean`, and the fixed-monoid Action setup in `CategoryTheory/Action/Limits.lean`. None states the category of quasi-coherent modules with descent along varying-space tensor pullbacks, or its underlying kernel/cokernel calculation. A nontrivial equivalence/construction would be required to apply those ambient results; this is not a Mathlib leaf. The item's previously recorded search records are preserved, with the three new distinct semantic queries appended from the actual log.

## Review by Q28

I read Stacks Tag 06VZ (`spaces-groupoids-lemma-abelian`, confirmed in `tags/tags`) and the adjacent `definition-groupoid-module` in spaces-groupoids.tex. The source uses quasi-coherent modules on the small etale sites, the map from t-pullback to s-pullback, the displayed composition law on the composable-arrow fibre product and the identity law. The subsequent `lemma-isomorphism` explains that the source's map is automatically invertible; the item explicitly requires this same invertibility. The source's proof obtains induced isomorphisms on underlying kernels and cokernels by flat pullback, then obtains the coimage/image criterion over U. It requires flat source and target maps without quasi-compactness or Noetherian hypotheses. Thus the item and cited theorem have the correct scope.

For the sole proof step I opened and read the full statement of `lem-sfb-flat-space-groupoid-kernels-cokernels`. It introduces the same S, U, R and structure maps, explicitly composes the second arrow then the first, uses exactly the same two descent equations and morphism equation, assumes flatness on etale scheme charts, and uses the same small-etale module sheaves and quasi-coherence notions. Consequently no equivalence theorem or change from scheme modules to space modules is hidden: the two categories are given by the same data. The cited statement literally supplies abelianity and the underlying module-sheaf kernels and cokernels with induced groupoid isomorphisms; it also explicitly says they are quasi-coherent. The excerpt in citations.json contains these clauses verbatim. The step is marked non-elementary because it invokes this substantive theorem, and its only proof dependency is that theorem. No off-unit tool is used.

I checked B1–B9: there are no new nodes needing statements, definition dependencies or Mathlib matches; the retained item is self-contained and its TeX and source remain intact. I checked C1–C8: every non-elementary input is the statement of the sole cited existing node, no proof-body information is borrowed, there is no use of an unstated flatness theorem, and the cited node currently has no proof dependencies that could point back here. I checked D1–D5: no new node restates this theorem, and this is reuse of a pre-existing stronger result as required by the duplicate rule, not relocation of the item into a new lemma. The one step has 1071 characters, below the long-step review threshold.

For E1–E7 I checked that no finiteness, separation or atlas-surjectivity assumption is introduced. The empty object-space case gives the zero module category, the identity groupoid gives QCoh(U), the zero morphism has its usual source kernel and target cokernel, and an identity morphism has zero kernel and cokernel. None needs additional hypotheses. The direction of alpha and order of composition agree in both statements, so no opposite-groupoid substitution is made. Nothing in the source or imported statement needed correction. The correction made was to supply the missing proof by the existing stronger theorem and keep the DAG from growing another duplicate.

## Unfinished work

None in this assigned one-level split. The cited existing node remains its own separately assigned stage-1 item; this report does not assert its proof is closed.
