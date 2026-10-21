# Q14 stage-1 delivery

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-supported-constant-exchange-normalization.json`: existing statement, now split into eight proof steps. The statement is unchanged. Mathlib verdict: no match for the whole statement.
- `citations.json`: a verbatim statement witness for every node cited by every proof step.
- `searches.jsonl`: six searches actually run by the required msearch command; the existing item's earlier searches are retained in its JSON.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean, compiler, Lake, library, repository, launcher, chapter, or unit changes.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the exact blueprint tag and the supported-constant/closed-exchange concepts. No project declaration states every clause of this item. Existing general adjunction facts and partial closed-support statements do not give this normalization and both comparison squares.

## WANTED

None. All sources used here are already in the read repository.

## Findings and changes

The item was an unsplit child of `lem-pur-supported-hom-pullback`, with no previous sandbox split or report. I copied that node, kept its entire statement and existing searches, and supplied its proof. No statement dispute or change was necessary. The essential point is to identify the *actual* canonical mate with the cokernel isomorphism: mere existence of some isomorphism would not prove the item.

I read the recorded chapter and unit and the current main-20261015 orientation statement and proof. The present item serves the geometric-fibre restriction and final etale-origin comparison of `thm-pur-affine-line-orientation`, as its existing ancestry records. It supplies an underived sheaf operation, without changing the affine-line/Kummer route or invoking purity. No SGA source is used.

Two tempting citations would have been wrong. `lem-weil-pbc-inverse-image-closed-pushforward-constant` is about topological spaces and sheaves of sets, not these etale/pro-etale module sheaves. `lem-weil-pbc-proetale-abelian-closed-support` requires a quasi-compact complement. I use neither. The existing `lem-pur-proetale-supported-constant-presentation` states precisely the constant-coefficient cokernel with no such hypothesis, and suffices here. The proof does not assume arbitrary-sheaf pro-etale localization without quasi-compactness or conservativity of ordinary geometric stalks on the pro-etale site.

## Mathlib and duplicate searches

The required searches were run with msearch.py, read, and recorded exactly with their tool and query. Both semantic phrasings were tried. The first LeanFinder results concern scheme/structure-sheaf restrictions. LeanSearch gives stability of scheme closed immersions and general constant-sheaf adjunction results. Loogle gives abstract adjunction facts. The second LeanFinder phrasing also finds the module pullback-unit transpose lemmas. I read `Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean` lines 72–107, `CategoryTheory/Sites/ConstantSheaf.lean` lines 125–160, `CategoryTheory/Adjunction/Basic.lean` lines 193–238 and `CategoryTheory/Limits/Preserves/Shapes/Kernels.lean` lines 252–274. These results are useful background, but do not state the item for the specified etale/pro-etale closed pairs, their presentations and both squares. The item is not a one-line specialization of any hit.

Before deciding whether any new lemma was needed I searched the whole DAG for Tags 095L and 03S6 and for constant presentations, exact inverse image and closed exchange. I used `tools/blueprint_refs.py ancestor` and whole-blueprint searches for `constant exchange`, `supported constant` and `extension by zero`. The first two have no matching blueprint statement; the broad last search contains the existing open extension comparison lemmas. More focused DAG reading found the existing generic constant-module pullback lemma. All non-elementary inputs could therefore be reused. No duplicate or new statement-only node was created, and `blueprint.same_as` remains the searched empty list.

## Not duplicates

No new nodes. In particular no new node restates the item's normalization clause or its comparison-square clause, and no new abstract cokernel or mate lemma is needed: those calculations are written in the proof steps.

## Review by Q14

I read Stacks `etale-cohomology.tex`, Tag 095L (`lemma-ses-associated-to-open`), including its adjunction/stalk proof, and Tag 03S6 (`lemma-shriek-base-change`), including the common-right-adjoint argument. I read `sites.tex`, Tag 00YV (`proposition-functoriality-algebraic-structures-topoi`), especially the fixed-ring scalar-endomorphism construction, and Tag 0H7J (`example-constant-sheaf`). I read `sites-modules.tex`, Tag 04JC (`lemma-flat-pullback-exact`) and Tag 04J0 (`lemma-localize-morphism-ringed-sites`); `proetale.tex`, Tag 09AF (`lemma-jshriek-comparison`); and `categories.tex`, Tags 0B65 (`lemma-transformation-between-functors-and-adjoints`) and 0DV0 (`lemma-compose-counits`). Milne LEC Section 9, proof of Theorem 9.4 on printed p. 67, gives the constant cokernel and kernel-of-restriction model. The pro-etale constant presentation is the existing agent-formulated extension, not an assertion falsely attributed to the etale Stacks tag. The additional mate and square calculations are marked agent-written in `proof_origin`.

For step 1 I opened and read the statements of the etale inverse-image definition, pro-etale inverse-image definition and site-comparison definition: they specify the intended adjunctions and the last two their geometric constructions. `prop-weil-pbc-inverse-image-modules-exact` explicitly supplies the etale constant-ring identification and exact module inverse image. `lem-pe-constant-left-module-inverse-image` supplies the corresponding result for arbitrary geometric morphisms of small sites, including compatibility of underlying units with compositions and localization. Its hypotheses apply because the sites have been made small in the stated larger universe, and all coefficients are fixed finite commutative ordinary rings. The constant-sheaf definition is actually sheafification of the constant presheaf; therefore preservation of each constant scalar determines the coefficient comparisons. No flatness assumption on the scheme morphism is being introduced.

For step 2 I read both cited presentation statements. `lem-weil-pbc-open-closed-short-exact` explicitly includes modules over an arbitrary commutative ring and specifies its maps as the open counit and closed unit; applying it to the constant sheaf gives exactly the etale sequence. `lem-pur-proetale-supported-constant-presentation` explicitly states the constant sequence, its actual restriction map, its cokernel interpretation, and the absence of a quasi-compactness hypothesis. Its finite commutative ring hypothesis holds for A. Thus neither citation is being used beyond its statement.

For step 3 I read all three cited open comparison statements: etale scheme pullback, pro-etale scheme pullback and etale-to-pro-etale comparison. They give canonical isomorphisms for arbitrary scheme maps/open immersions and finite commutative coefficients (ordinary sheaves are complexes concentrated in degree zero when that statement uses complexes). The two cited open adjunction statements give precisely the Hom bijections needed for the transpose calculation. The localization lemma gives both the inverse-image and sectionwise direct-image comparisons of ringed sites, with no quasi-compactness requirement. `lem-sf-open-comparison-unit-normalization` explicitly identifies the actual comparison and its unit equation, rather than giving an arbitrary isomorphism. The written transpose of the two candidate counit maps is the same map q_U: the only cancellation is the adjunction triangle identity. I checked the directions: b goes from L j_! to j'_! L_U, while its inverse is the transpose of the pulled-back open unit. This avoids reversing the canonical comparison.

For step 4 I read the underived-exchange and general adjunction-mate definitions. The former specifies the etale exchange by the pulled-back closed counit; the latter is the same formula in arbitrary categories and therefore defines the pro-etale and comparison analogues as well. I checked the types r'L -> L_Z r and LP -> i'_*A_Z'. The transpose of rho is q_i, and the triangle identity says epsilon_i r(rho)=q_i. Consequently the two transposes calculated in the step have the same domain r'LA_X and target A_Z'. Their equality is the already cited constant-unit coherence. This is a direct definition/triangle calculation, not a missing closed base-change theorem concealed in a definition citation.

Step 5 uses only steps 1–4 and the cokernel universal property. I checked both inverse equations after precomposition with their respective cokernel arrows. This proves uniqueness for every candidate morphism satisfying the normalization, hence also for the actual canonical mate. No separate lemma is hidden in this short argument.

For step 6 I read the full statement of `lem-weil-pbc-comparison-pullback`: it gives the natural inverse-image isomorphism and its compatibility with identities, composites and the chosen Cartesian identifications. I checked the two precomposition calculations with N'H(rho), including k's naturality at rho. This map is epic because the two inverse images are exact. The coefficient equality uses the same scalar-preserving comparison, not a new choice of k. Thus cancellation proves the displayed square with exactly its stated direction.

For step 7 the cited localization statement actually gives the comparison of restricted direct images, not just an equivalence of sites. Naturality of its unit makes the restriction square commute. The cited support-cohomology definition explicitly defines supported sections as the kernel of restriction in either topology; restricting a section map to that kernel is therefore the claimed lambda for every M. No derived claim or acyclicity assumption is made here.

For step 8 I read both direct-image definitions and the site-comparison definition. Their composites evaluate a sheaf on the same base-changed object V times_X X', with identical restriction maps and constant scalar actions. The composite-adjunction definition specifies the two units. `lem-weil-pbc-conjugate-iso-unit-equation` states the exact unit-preservation equation for the canonical conjugate isomorphism; its adjunctions have the same source and target here, with the canonical sectionwise identification of right adjoints. Evaluating this equation on a section is the equality written in the step. Step 7 ensures the intermediate sections still have support, so restriction to kernels proves the supported-section square. This also spells out why the unit-normalized coherent k, not an arbitrary natural isomorphism of the endpoint functors, is being used.

I checked edge cases of the unchanged statement: Z empty gives P=0 and zero supported sections; Z=X gives j_!=0, P=A_X and ordinary section pullback; the identity h gives identity normalized exchange; X' empty gives the zero target category and its unique exchange. Nilpotent structure on Z is harmless because every comparison is formed with the actual closed fibre product and the specified site operations, never an unjustified factorization by underlying point sets. Non-quasi-compact U is permitted by the actual presentation node and the open comparison statements. An arbitrary M is used only for sections and their kernels, so no constructibility, Tor amplitude, injectivity or derived finiteness has slipped in.

I checked delivery-errors B–E against the finished files. There are no new-node form, duplicate, statement-only, or elementary-node issues because no new node is created. Every cited statement was opened; citations.json contains the actual verbatim statements, including hypotheses. No step takes a construction solely from the proof of another node. The additional arguments are explicit adjunction, cokernel and kernel calculations; no long step exceeds 2,000 characters. Generic tools outside the unit route are justified in `split_report.tool_uses`, without changing maintainer-owned top-level `tool_uses`. The proof has no use of a descendant supported-Hom lemma and does not presuppose the compatibility it proves.

## Unfinished work

None in this one-level split. Existing non-Mathlib dependencies retain their own independent stage-1 status. Validation and delivery use only the authorized remote tools.
