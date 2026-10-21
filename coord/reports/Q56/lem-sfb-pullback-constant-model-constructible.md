# Stage-1 repair: lem-sfb-pullback-constant-model-constructible

## Files written

All node files are under dag/nodes/sec-six-functors-basics/ in this sandbox.

- lem-sfb-pullback-constant-model-constructible.json: item statement unchanged; split into five assembly steps, 2305 proof-text characters, longest step 517 characters.
- lem-sfb-scalar-presentation-cokernel.json: new statement-only unsplit lemma, non-Mathlib. A specified ordinary scalar-module presentation becomes the cokernel of that same matrix after constant sheafification and extension to the coefficient sheaf.
- lem-sfb-scalar-matrix-inverse-image.json: new statement-only unsplit lemma, non-Mathlib. Inverse image preserves the prescribed scalar entries between finite free coefficient modules and their cokernel diagram.

The two new nodes have empty proof and proof_deps, null proof_origin, and no split_report. Their sources, full statements, definition dependencies, blueprint references and actual Mathlib search records are retained. The earlier helper arguments are preserved below as notes for their next stage-1 workers, outside the node files. The earlier report is retained in report-before-statement-only-repair.md in the sandbox; citations-new-nodes.json and repair.py remain historical sandbox artifacts. The current parent citation certificate is citations.json. searches.jsonl is the original unedited command log.

## Attachments

None. The exact blueprint tag and the constructible-pullback and scalar-matrix notions were searched in lean/WeilConjectures. No exact finished project declaration was found for this item or the helpers. I read lean/Sheaf/AlgebraicGeometry/PullbackConstantModelConstructible.lean: AlgebraicGeometry.ProEtale.pullback_constantModelConstructible still ends in sorry. The private scalarRegular_entry, scalarFreeIso and scalarMatrix_map in FiniteConstantLocalModel do not give exact public WeilConjectures statements of either new node. Existing partial constructions therefore do not supply an attachment.

## WANTED

None; the needed blueprint and Stacks sources are locally present.

## Fault and repair

The human returned the original item for a 3942-character proof, especially Steps 3 and 4. The retained attempt had already extracted those two calculations but incorrectly made the new nodes split. Its dry runs were refused because new nodes must be unsplit or mathlib. The CURRENT route note explicitly resolves this: extracted arguments must be NEW statement-only unsplit nodes, with their proofs left to the next stage-1 workers. I followed that instruction, cleared the two helpers' proof fields and moved their arguments into this report. This is a substantive parent re-split with two new lemma interfaces; the parent is not merely relabelled or rebased.

I compared the retained parent with the live read clone: only proof, proof_deps and split_report differ. Its statement, statement dependencies, source, recorded Lean and maintainer-owned fields remain unchanged. Both helper ids are still absent in the live DAG. No target statement, unit route or coefficient convention changed. The original C4 issue remains repaired: the existential matrix equivalence of det-def-sfb-constructible-local-model does not justify retaining a prescribed P and its chosen presentation. The new presentation lemma states that exact stronger compatibility; the matrix lemma independently supplies the entrywise pullback square.

The mandatory first action for retained work was deliver.py --no-push. I polled its single process until exit 1; it reproduced exactly the two status errors. Only after that process exited did I edit the sandbox. The final dry run and delivery result are recorded below when completed.

## Searches and source readings


I read the chapter and unit records sec-six-functors-basics and sk-prop-proper-base-change-unbounded, the current main-20261015 parent pullback proof, the local-model source sk-def-sfb-constructible-local-model.md, and the coefficient-morphism source sk-def-sfb-coefficient-morphisms/_section.md. The blueprint's phrase “via the local coefficient models on strata” is the place both helpers make precise; the other place “pull back the stratification” remains the existing argument.

For the presentation helper I read Stacks sites-modules.tex Tag 03CY, sites-modules-lemma-sheafification-presheaf-modules, including its following adjunction paragraph. The scalar-extension adjunction is supplied by def-sfb-modobj-extend-restrict-adjunction. For the matrix helper I read Stacks Tag 03D2, sites-modules-lemma-pullback-module, and Tag 03D3, sites-modules-lemma-adjoint-push-pull-modules: inverse image transports the action, and module inverse image is an adjoint. Colimit preservation uses the existing node for Stacks Tag 0038, categories-lemma-adjoint-exact (1). The retained helper argument notes are agent-written because their particular condensed scalar-matrix comparisons assemble these results; no Stacks lemma is misrepresented as literally stating that comparison. For unchanged Step 1 I reread Stacks 054I, morphisms-lemma-inverse-image-constructible, at morphisms.tex:4340, and the corresponding existing DAG statement. No prohibited SGA source is used.

DAG searches covered all chapters, both key words and the relevant Stacks tags, together with blueprint_refs.py ancestor and searches for scalar matrix, constant local model, finite presentation, coefficient morphisms, scalar presentation, matrix cokernel, scalar sections, specified presentation, scalar matrix pullback and matrix. I read the statements of the closest candidate nodes named below. Fresh Mathlib searches were run through msearch.py only, with two semantic phrasings for each new node and with LeanSearch, LeanFinder, Loogle and grep. Each node records the actual queries and logged result names. No service outage was claimed as a negative answer. The initial invalid Loogle type-class query is recorded as invalid, not evidence of absence.

Mathlib candidates were read in Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean (presentationOfIsCokernelFree at 114 and Presentation.map at 180), PullbackContinuous.lean (pullback at 53), and PullbackFree.lean (pullbackObjFreeIso at 118 and the injection formula at 125). The general presentation transport and free-module pullback are supporting ingredients. They do not themselves identify the ordinary scalar-section map from Lambda(*) for a pulled-back condensed coefficient ring. That compatibility is precisely what the new proofs establish. They therefore do not give a one-line specialization proving either entire new statement.

## Not duplicates


lem-sfb-scalar-presentation-cokernel vs det-def-sfb-constructible-local-model: the existing node gives an existential equivalence on covers; the new node fixes P, q and A in advance and asserts that E_U(q) is the cokernel projection of this exact scalar matrix, on any scheme U without a cover hypothesis.
lem-sfb-scalar-presentation-cokernel vs lem-weil-pbc-regular-extension-comparison: the existing node concerns extension of one regular module and its scalar endomorphisms; it does not give a constant-sheaf presentation or preservation of a specified cokernel. It is cited as an ingredient.
lem-sfb-scalar-presentation-cokernel vs lem-sfb-integral-continuous-cokernel-local-model: that node concerns an integral finite extension and its continuous-model normalization, whereas this node starts with an arbitrary commutative condensed ring and its ordinary scalar-section presentation.
lem-sfb-scalar-matrix-inverse-image vs sk-def-sfb-coefficient-morphisms: the existing node defines the natural coefficient comparison and says it is a ring isomorphism; the new node proves the finite-free scalar-entry square and resulting cokernel comparison.
lem-sfb-scalar-matrix-inverse-image vs lem-weil-pbc-regular-extension-comparison: the existing theorem handles extension of scalars and one regular endomorphism satisfying a compatibility equation. The new theorem proves that compatibility for inverse image of condensed scalar sections, then handles all matrix entries and cokernels.
lem-sfb-scalar-matrix-inverse-image vs new-unbounded-pullback-finite-constant-local-model: that statement retains finitely presented condensed models on covers, whereas the new lemma is about an ordinary Lambda(*)-valued matrix, no local-model or covering predicate, and its explicit pullback square.
lem-sfb-scalar-matrix-inverse-image vs lem-sfb-proetale-fp-local-models-pullback: that node assumes discrete Noetherian coefficients and asserts preservation of a local-model predicate. The new node permits any commutative condensed ring and proves the specified scalar-matrix formula.
lem-sfb-scalar-matrix-inverse-image vs lem-sfb-geometric-inverse-image-constant-module: that theorem pulls back a constant R-module sheaf. Lambda_U here need not be the constant sheaf of the discrete ring Lambda(*); the new node concerns its regular modules and canonical scalar-entry actions.
lem-sfb-scalar-matrix-inverse-image vs lem-weil-pbc-condensed-local-presentation-matrices: that node descends local presentations over an algebraic closure to some finite coefficient field and cover; it does not give a prescribed scalar matrix's pullback.

The two new nodes also differ from the item itself: neither mentions constructibility or a stratification, and neither alone gives its conclusion. The item needs both calculations plus its original geometric statements. The new helpers do not cite the item or any of its users.

## Review by Q56

I read coord/delivery-errors.md B--E in full, GOAL.md, the three blueprint levels in SETUP.md, the chapter and unit records, the main-20261015 pullback proof, and the two source definitions named above. The parent follows the unit's local-model pullback step without replacing the route. I checked its unchanged admissible coefficients against the stated Lean signature, including the finite-subextension-valued algebraic closure convention. I introduced neither an invertibility-of-ell hypothesis nor a discreteness assumption on the coefficient sheaf.

For Step 1 I opened lemma-constructible-pullback-stratification and lem-pur-scheme-constructible-preimage. The former supplies finite locally closed base-changed strata and their inverse-image subsets; the latter supplies constructibility for an arbitrary scheme morphism. Stacks 054I (morphisms-lemma-inverse-image-constructible) has precisely that unrestricted hypothesis, so I did not infer constructibility merely from local closedness.

For Step 2 I opened det-pe-topos-functoriality-inverse-image and used exactly clause 1, which sends an entire covering family to a covering family for every scheme morphism. The map between old and new strata need not be weakly etale. Its off-unit citation is the already accepted generic site tool, declared again in split_report.tool_uses; it does not replace a unit argument.

For Step 3 I read def-sfb-finitely-presented-module: it gives finite free modules and a cokernel presentation. In ordinary R-modules a map between the specified finite free bases is a scalar matrix, by evaluation on those finitely many basis vectors. The new lem-sfb-scalar-presentation-cokernel explicitly fixes q, P and A and applies to both U and V, which supplies the two cokernels of that very presentation. It does not rely on choosing an unrelated existential matrix. Its statement introduces Lambda, its scalar ring R, the scheme, constant sheaves, canonical scalar map, matrix and cokernel map, with definition nodes for each construction. The source local-model definition supplies the scalar-extension convention; Stacks 03CY, sites-modules-lemma-sheafification-presheaf-modules, and its following adjunction paragraph support the preserved argument below. This is a genuine algebraic comparison with arbitrary schemes and ranks, strictly below the constructibility result.

For Step 4 I read the entire new lem-sfb-scalar-matrix-inverse-image statement and sk-def-sfb-module-pushforward-pullback. The former explicitly supplies the scalar-matrix square AND the resulting cokernel isomorphism; no preservation theorem is inferred just from the definition of a pullback. The latter explicitly states (g composed with f)^* is isomorphic to f^* composed with g^*. The two composites from V to Y agree by the defining fibre product, so these composition isomorphisms give the displayed restriction of g^*M. The helper statement introduces its arbitrary h, both coefficient rings, their canonical comparison, ranks and scalar matrix, with definition dependencies. I checked the coefficient-morphism definition and point-pullback-composition definition: the comparison is monoidal and natural, so its scalar compatibility is a well-posed claim, not a choice of some ring isomorphism. Stacks 03D2 (sites-modules-lemma-pullback-module), 03D3 (sites-modules-lemma-adjoint-push-pull-modules), and 0038 (categories-lemma-adjoint-exact) support its retained report argument. Its finer proof belongs to the next stage-1 worker under the explicit route note.

For Step 5 I opened sk-def-sfb-constructible and checked its qcqs finite-stratification clause. The previous four steps supply exactly those witnesses with the original index sets and P's. This is elementary packaging of already established data, which is the only step marked elementary. Every parent citation has its own verbatim statement quote in citations.json; I checked completeness against every uses list and checked that proof_deps is their union. No step needs the proof of a cited node.

I checked B1--B9 on both new files: self-contained TeX statements, definition citations, source and exact blueprint place, logged searches read, null Mathlib match and unsplit status, no proof steps, and no invented searches. The old queries are reused because neither helper statement nor search question changed. I re-ran whole-DAG and blueprint duplicate searches, read the candidate statements listed above, and verified neither helper is an existing node or a clause restating the parent. The helpers assert no constructibility or stratification conclusion. The Mathlib candidates concern general presentation transport or free sheaf pullback; they do not identify these condensed ordinary scalar maps without a further comparison theorem. Thus neither entire helper is a one-line specialization. No prohibited SGA source is used.

Hypotheses and edge cases: the helpers allow arbitrary U,V and do not use qcqs; only the parent final constructibility criterion uses qcqs Y'. Constant scalar extension is used for cokernels, not kernels, so no flatness or injectivity is needed. For m=0 the cokernel is free, for n=0 it is zero; A=0, P=0, the zero ring and h=id give the expected diagrams. For empty schemes the coefficient-section ring is zero, and the module diagrams and comparisons remain valid. Empty strata and base-changed cover members do not require deleting the given index sets. These checks apply to integral, field and finite coefficients alike because the helper statements use only a commutative condensed ring.

The requested coarseness repair is complete in the parent: its five proof steps are all under 600 characters and its total is below 3000. The new unsplit nodes intentionally carry no proofs, as the current route note requires. Their prior short arguments are retained below solely as report material for continuation. No Lean file, compiler, Lake/build, launcher file, shared repository file, or git command in the shared repository was used for edits.

## Retained helper arguments for the next stage-1 workers

These are the earlier attempt's argument notes, preserved rather than discarded. They are not proof fields of the new nodes and are not claimed as completed splits.

### lem-sfb-scalar-presentation-cokernel

1. Work in ordinary sheaves of modules via [def-weil-pbc-internal-abelian-sheaf-module-equivalence]; its equivalence is the identity on underlying abelian sheaves and actions on sections. The sheafification adjunction [lem-pc-sites-module-sheafification-interface] gives $\operatorname{Hom}_{R_U}(Q_U,N)=\operatorname{Hom}_R(Q,N(U))$: a map from the constant presheaf is determined by its component at the terminal object $U$, and all other components are its restrictions. Thus $Q\mapsto Q_U$ is left adjoint to scalar-module global sections. The equivalence carries these Hom bijections back to internal modules.

Inputs: def-weil-pbc-internal-abelian-sheaf-module-equivalence, lem-pc-sites-module-sheafification-interface

2. Compose the constant-module adjunction with extension/restriction [def-sfb-modobj-extend-restrict-adjunction]. This makes $E_U$ a left adjoint. By [lem-weil-pbc-left-adjoint-preserves-colimits] it preserves the given cokernel and finite coproducts (only finite index categories occur). Constant sheafification sends the regular $R$-module to the regular $R_U$-module, by its action on constant sections. The regular-module comparison [lem-weil-pbc-regular-extension-comparison] then identifies $E_U(R)$ with $\Lambda_U$. Taking finite coproducts gives $E_U(R^r)\cong\Lambda_U^r$.

Inputs: def-sfb-modobj-extend-restrict-adjunction, lem-weil-pbc-left-adjoint-preserves-colimits, lem-weil-pbc-regular-extension-comparison

3. On the regular module, constant sheafification sends multiplication by $a\in R$ to multiplication by its constant section. The endomorphism clause of [lem-weil-pbc-regular-extension-comparison] sends it to multiplication by its image in $\Lambda_U$. Apply this to every entry $a_{ij}$ and the coproduct injections and projections. The image of $A$ is exactly $A_U$; the preserved cokernel from Step 2 is therefore the asserted diagram with $E_U(q)$. No injectivity of $A$ or flatness of $\Lambda_U$ over $R_U$ is required.

Inputs: lem-weil-pbc-regular-extension-comparison

### lem-sfb-scalar-matrix-inverse-image

1. By [sk-def-sfb-module-pushforward-pullback], $h^*$ first transports abelian inverse image to module objects and then extends along $\alpha_h$. Transport sends the regular module to the regular $h^{-1}\Lambda_U$-module: its action is the pulled-back multiplication. Apply [lem-weil-pbc-regular-extension-comparison] to obtain $e_1:h^*\Lambda_U\cong\Lambda_V$. The pullback adjunction and [lem-weil-pbc-left-adjoint-preserves-colimits] give the comparisons $e_r$ by finite coproducts and also preservation of cokernels.

Inputs: sk-def-sfb-module-pushforward-pullback, lem-weil-pbc-regular-extension-comparison, lem-weil-pbc-left-adjoint-preserves-colimits

2. For $a\in R$, represent its section by $s_a:\mathbf Z\to\Lambda$ on the condensed point. Its scalar section on $T$ is $p_T^*(s_a)$ with the unit comparison [sk-def-sfb-pulled-back-coefficients, det-def-sfb-constructible-local-model]. By [sk-def-sfb-coefficient-morphisms], $\alpha_h$ is the component of the monoidal natural isomorphism $h^{-1}p_U^*\cong p_V^*$ [sk-def-sfb-pullback-from-point-comp]. Naturality at $s_a$, and the unit comparison, send the pulled-back section to precisely the section defined by $a$ on $V$. As $\alpha_h$ respects multiplication, the endomorphism clause of [lem-weil-pbc-regular-extension-comparison] identifies multiplication by $a$ under $e_1$.

Inputs: sk-def-sfb-pulled-back-coefficients, det-def-sfb-constructible-local-model, sk-def-sfb-coefficient-morphisms, sk-def-sfb-pullback-from-point-comp, lem-weil-pbc-regular-extension-comparison

3. Apply Step 2 to each $a_{ij}$. Under the coproduct comparisons, functoriality on injections and projections identifies every entry of $h^*(A_U)$ with the corresponding entry of $A_V$, proving the displayed square. By Step 1, the image of the cokernel diagram is a cokernel diagram; the square identifies it with the diagram for $A_V$. The universal property gives the required isomorphism and compatibility with projections, including when either rank is zero.

Inputs: 

## Checks and unfinished work

The initial dry run reproduced only the two new-node status failures, now repaired according to the explicit current route note. Final dry-run and push results will be appended here. The helper proofs are future stage-1 items by design; there is no unfinished parent assembly or statement change.

## Final dry run

The repaired deliver.py --no-push process exited 0 and printed: OK (not pushed) deliver/Q56/lem-sfb-pullback-constant-model-constructible at 6efe9f87cf0: preflight passed. This ran the required server preflight, including check_dag and review_split, on the repaired sandbox. The earlier status conflict is resolved by the current statement-only route note. The push is the next authorized delivery action.
