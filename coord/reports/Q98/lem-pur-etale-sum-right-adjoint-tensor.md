# Q98 stage-1 repair: lem-pur-etale-sum-right-adjoint-tensor

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-etale-sum-right-adjoint-tensor.json: unchanged statement, short assembly, status split.
- dag/nodes/sec-smooth-purity/lem-pur-etale-sum-unit-evaluation.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-smooth-purity/lem-pur-adjoint-projection-tensor-transfer.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-smooth-purity/lem-pur-etale-normalization-comparison-coherence.json: statement, unsplit, no Mathlib match.
- citations.json: verbatim statement extracts for every step citation.

## Attachments

None. WeilConjectures has no declaration with the item's blueprint tag. The Sheaf module EtaleSumRightAdjointTensor has sorry in isIso_etaleTensorProjection (line 108), the main theorem (207), refinement (242), and open restriction (332). ProjectionTensorMap.lean supplies generic tensor-map properties, not this conditional conjugate/unit calculation, and is not an attachment of the full item.

## WANTED

None. All source files used here are present.

## Return repaired and work allocation

The return is the human's 2026-10-21 re-split decision, applied 2026-10-22: the 7605-character proof must become an assembly of at most 3000 characters, with at least two comparable new statement-only nodes. The sandbox initially contained only launcher brief markers, not a retained delivered node or report; the first required dry run exited with 'no node files'. I copied the current read-clone item, whose nine proof steps match the return exactly. No git command ran in the read clone. The current statement and all unrelated fields are retained.

Three independent new obligations are now exposed. Unit-evaluation takes old Steps 2–3 (2207 characters): the generator evaluation, passage through sheafification, flat/K-flat models, termwise counit, signed total differential, and localization uniqueness. Tensor-transfer takes Steps 1 and 4–6 (2750 characters): conjugacy, the Hom-bijection transport, inverse-projection normalization, naturality at rho of the unit, symmetry/unitor, and final transposition. Comparison-coherence takes Steps 7–9 (2648 characters): refinement conjugates and cocycle, the canonical open comparison from nested-summand composition, coefficient-unit comparison, and tensor-family cancellation. Its tensor-family clause is conditional on normalization, so it does not assume or restate the parent theorem. All three have proof=[], proof_deps=[], proof_origin=null and status unsplit: later workers supply their proofs. The full old argument is reproduced below, with every step assigned to its new node, rather than silently shortened.

The parent has three application steps; after the current-base repair its proof-text character count is 2050. No individual parent step exceeds 2000 characters. No statement dispute is needed and no hypothesis or conclusion was weakened. In the formal transfer statement the symmetry-unit relation is explicit; we do not infer it from a bare definition of a tensor swap or discard a Koszul sign.

## Repair of the landing refusal (2026-10-22)

The current return says the reader approved the delivery, but landing refused the side-project completion that had not been promoted to the live DAG. The retained ready record identifies the earlier delivery head as `3cfdc5cd450`. I continued the retained four JSON files, report, citations and all seventeen logged searches; I did not regenerate or discard that work. The current released stage-1 repair note still orders this unchanged statement to be re-split with at least two new statement-only nodes and an assembly of at most 3000 characters. Its `keep_plan: true` preserves the route.

I compared the retained item field by field with the current read-clone DAG. Before this repair only `proof`, `proof_deps` and `split_report` differed. In particular the statement, statement dependencies, blueprint ancestry, Lean records and maintainer-owned fields agree with the current item. All nine proof texts in the current DAG occur verbatim in the allocation appendix below, so the original argument remains fully available. All three proposed child ids are still absent from the current DAG. The required delivery tool builds the new commit on its freshly fetched current base, rather than re-pushing the old head.

I re-read all 33 external statements cited by the four retained nodes, including all statement dependencies, against the current DAG. In parent Step 1, `lem-pur-etale-support-map-compatibility` still supplies the same generator-normalized projection square in clause (2), for finite coefficients and Noetherian schemes, precisely the hypotheses of the parent. Its clause (1) continues to use the specified proper exchange and inverse sum base-change map. `lem-sf-ringed-derived-closed-symmetric-monoidal` supplies the signed tensor symmetry and unitors on total complexes. I made the remaining elementary specialization explicit in Step 1: the coefficient unit has degree zero, so the signed swap followed by the left unitor sends $x\otimes a$ to $ax$, exactly the right unitor. Thus the extra unit/symmetry hypothesis in the abstract transfer node is verified, rather than inferred from a bare tensor swap. Steps 2 and 3 still apply the retained self-contained transfer and comparison statements with the same functors, maps and hypotheses; every entry of citations.json remains a verbatim current statement extract.

For the unit-evaluation child, the current sheaf projection, totalization, and flat/K-flat statements still apply over an arbitrary commutative ring and arbitrary schemes with separated etale finite-type e. In particular no finite-coefficient or Noetherian hypothesis was silently imported into this child. For the transfer child, the current conjugate and mate definitions retain the direction $(d^{-1})^c:G\to T$ and the same bijections and inverse laws. For the comparison child, the current unbounded compact-support comparison statement includes refinement identity/cocycle, the normalized proper/open tower composition and Cartesian exchange. The current quasi-finite proper-support statement explicitly identifies etale support composition with the nested-summand comparison. The base-change module statement identifies the sum-extension comparison in the required direction, and tensor pullback remains natural on unbounded objects. Open subschemes of the Noetherian base are Noetherian; the pulled-back etale map remains separated and of finite type. These are the hypotheses needed for the open comparison and its unit object, including the $G_{e'}(u_g)$ in xi.

The first retry dry run exposed a newer same-tag node, `lem-sf-etale-graph-projection-arbitrary-base`. I opened its complete current statement. It allows arbitrary schemes and non-quasi-compact open compactifications but assumes a finite coefficient ring, fixes a graph comparison $a:S\to F$, and concludes $P^{-1}a=(a\otimes1)\kappa$. It asserts neither the sheaf coefficient-unit evaluation equation nor its arbitrary-ring derived extension. It also asserts no right-adjoint open comparison, refinement equation for rho and eta, or conditional transport of normalized tensor families. Thus it does not replace either geometric child. The explicit pairwise distinctions have been added to `## Not duplicates`; the three child statements and their logged search questions are unchanged, so repeating those Mathlib searches is unnecessary.

I re-opened the blueprint locality proof Step 1 and Stacks Tags 0GKF (`lemma-f-shriek-projection`, more-etale.tex) and 03S6 (`lemma-shriek-base-change`, etale-cohomology.tex), checking their tag/label mappings. The existing agent-written expansions remain expansions of those generator and base-change inputs, with no SGA source. I rechecked the formulas at identity e, empty source, a two-sheet disjoint union, an open immersion, zero coefficients, K=0 and shifted K. Degree-zero coefficient units introduce no Koszul sign; the general tensor symmetry remains signed. This repair preserves the three-way allocation and changes the actual parent assembly, the current-base split report, and this review/report, rather than submitting an unchanged re-push.

## Search audit

I searched the whole DAG by notions and tags (0GKF, 03S6), and used blueprint_refs.py searches for sum evaluation, conjugate tensor, projection tensor, etale normalization, open restriction, unit evaluation, adjunction projection, refinement normalization, sum unit, projection conjugate, normalization restriction. I read the hits' statements rather than their proof bodies. The blueprint ancestor is thm-pur-composition-coherence, through the item's recorded two ancestors. No blueprint node states one of the three new obligations. I also read the existing lem-asd-etale-sum-extension-tensor statement in full: its reverse-order derived counit compatibility is restricted to finite rings and Noetherian schemes, so it does not cover the new unrestricted sheaf-and-derived unit-evaluation statement. This close overlap and the exact difference are disclosed below.

Mathlib searches are actual msearch.py invocations, preserved in searches.jsonl. Each child records semantic searches with two phrasings, Loogle, source grep and the attempted LeanSearch query. LeanSearch was rate-limited and is recorded unavailable, not as no match. Generic conjugateEquiv and monoidal-adjunction hits were read in Mathlib/CategoryTheory/Adjunction/Mates.lean, Monoidal/Functor.lean (1020–1042), and Monoidal/Closed/Basic.lean (225–270). The first handles conjugates but not the compatible arbitrary projections; the second assumes monoidal structures on the left adjoint and gives induced lax-structure identities, whereas F and S here are arbitrary left adjoints with module projection comparisons. The third concerns internal Hom precomposition. None specializes in one line to the new statements. The remaining semantic hits concern Mayer–Vietoris, Ext exactness, ordinary structure-sheaf restriction, Profinite or condensed sigma comparisons, not these ordinary unbounded etale maps.

## Review by Q98

I read the current blueprint locality proof Step 1, which calls the etale normalization immediate, and the chapter/unit records. This repair stays within the original etale sum/evaluation subargument of the existing purity route. I read Stacks more-etale.tex Tag 0GKF, label lemma-f-shriek-projection, especially its actual pure tensor (Z,s) tensor t mapping to (Z,s tensor f-inverse t), and etale-cohomology.tex Tag 03S6, label lemma-shriek-base-change, including the adjoint-based proof. I verified both tag-label mappings in tags/tags. These give the generator and open base-change inputs; the categorical and unbounded expansions remain agent-written, as the parent already records. No SGA source is used.

For the unit-evaluation node, the source normalization agrees with the sheaf generator node: a lift (s,b) tensor h goes to b h after either composite. Its statement is about sheaf maps and derived natural transformations, not equality of all sheaf sections with presheaf sums. The exact inverse-image restriction node identifies TH on a lift with H(W), with the constant-A action respected. For the unbounded conclusion I read the statements of K-flat resolution, pullback preservation, sum flat/K-flat preservation, totalization, termwise adjunction, tensor descent, and localization uniqueness. They give precisely the flat-term models, total map and counit used by old Step 3; the coefficient unit is concentrated in degree zero, so its tensor differential is b d_H(h). No boundedness or finite-coefficient assumption is hidden in this child.

For the tensor-transfer node, all categories, functors, adjunctions, projections, unit and symmetry maps are introduced in its own statement. I checked the inverse d direction against the conjugate definition. The map q has domain F(TK tensor W), symmetry target F(W tensor TK), inverse-projection target FW tensor K, and final target K. Both projection and evaluation identities are explicit hypotheses. The conclusion includes the intermediate q d-inverse formula, the transported Hom bijection, and the final natural tensor identity, so the four old assigned steps are all actual obligations, rather than erased calculations. Taking C=D and F=S=T=G=id reduces the formulas to unit coherence; rescaling d in module categories rescales rho and eta consistently and still gives the same equality. No faithfulness is assumed.

For comparison-coherence I read the statements of proper-support/sum comparison, support-map compatibility, compact-support comparisons, mate-pasting, and the existing sum-right-adjoint coherence node. Refinement t goes F^c to F^cprime and its inverse conjugate goes G^c to G^cprime; this makes dprime t=d and rhoprime r=rho well-typed. In an open square, the left comparison goes Dg! F_eprime to F_e Dh!, hence its conjugate goes h*G_e to G_eprime g*. The displayed chi formula has exactly that type. xi includes G_eprime(u_g), so its target is W_eprime, not merely G_eprime(g*A_X). The tensor-family clause assumes normalized families, not the theorem being proved; its two comparison equalities follow by postcomposition with invertible rho. Open subschemes of the Noetherian schemes satisfy the hypotheses, and eprime is again separated etale finite type. The original argument checked the projection restriction on generators and compact-support exchange, and both are preserved explicitly in clause (2).

Parent Step 1 cites the new unit-evaluation statement for the actual evaluation identity, support-map-compatibility (2) for d P=p(d tensor 1), and the ringed-derived symmetric-monoidal statement for the signed symmetry and unitors. I read each of these statements; each says exactly what is used. The derived ringed-site statement is applied on small etale sites in the fixed module universe; no large-index colimit is introduced. Parent Step 2 cites the formal transfer statement, with F,S,G,T and both projection inputs exactly those of Step 1. Its q is the parent's specified inverse transpose, so the resulting tau is the parent's tau, rather than a differently normalized map. Parent Step 3 cites comparison-coherence, first obtaining the specified r and chi and projection compatibility, then applying its conditional tensor-family clause using the normalization just proved for every compactification and for eprime. All final comparisons are therefore identities of actual derived maps. citations.json quotes every cited node verbatim.

I tested the geometric children with e=id, empty U, a two-sheet disjoint union U=X disjoint-union X, an open immersion, K=0, and shifts of K. Evaluation is respectively identity, the unique zero map, finite-sum fold, and extension-by-zero evaluation. In the empty case all U-side maps are the unique maps on the zero category; the claimed isomorphisms there do not force anything nonzero. The generic transfer uses signed symmetry in a symmetric category, so shifts require no unrecorded deletion of signs. Identity refinements give r=id, composing refinements composes their conjugates in the recorded direction, and g=id makes chi the canonical identity after the unit/composition comparisons. Empty open restrictions are again zero-category identities.

Against delivery-errors B–E, I checked self-contained hypotheses, notions and actual definition dependencies, single-escaped TeX, exact Stacks labels, real logged searches, and no new proof bodies or proof dependencies. The three children have different inputs and arguments: geometric evaluation, conditional abstract transfer, and comparison of normalized families. None contains the whole parent's geometric assertion. Non-elementary inputs of the parent are cited; no child cites the parent or another new child. The old nine-step reasoning is retained in the allocation appendix. I did not add a statement from a proof body of a cited node. The only extra generic tool in the parent is the ringed-derived symmetric-monoidal structure, declared in split_report.tool_uses; it changes no purity route.

## Not duplicates

lem-pur-etale-sum-unit-evaluation vs lem-sf-etale-graph-projection-arbitrary-base: the existing node assumes finite coefficients and an open/proper factorization and proves compatibility of its specified graph comparison with the abstract projection mate kappa. The new node proves the coefficient-unit sum/evaluation equation both on sheaves and as an unbounded derived natural transformation for arbitrary commutative coefficients, without any compactification; no such evaluation equation is asserted by the existing node.

lem-pur-etale-normalization-comparison-coherence vs lem-sf-etale-graph-projection-arbitrary-base: the existing node proves the graph/projection square for one factorization and contains no right-adjoint refinement or Cartesian-open comparison. The new node identifies the conjugate right comparisons, their unit normalizations and cocycle, and transports an arbitrary family satisfying the stated tensor normalization across these comparisons.

lem-pur-etale-sum-unit-evaluation vs lem-coef-etale-open-total-tensor: the existing statement is 'Unbounded total tensor projection for etale extension without quasi-compactness'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs def-pur-etale-projection-data: the existing statement is 'Canonical section and stalk comparisons for etale sum projection'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-pur-compact-support-graph-tensor-evaluation: the existing statement is 'Tensor evaluation of the normalized compactification graph'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-pur-etale-projection-kan-comparison: the existing statement is 'The existing canonical Kan-extension etale projection comparison'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-pur-etale-projection-section-normalization: the existing statement is 'Section normalization of the canonical Kan projection isomorphism'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-pur-etale-projection-stalk-normalization: the existing statement is 'Section formula implies the normalized geometric-stalk square'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-pur-etale-sheaf-projection-map: the existing statement is 'Etale sum-extension sheaf projection formula'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-pur-etale-sum-flat-aux: the existing statement is 'Etale sum extension preserves flat sheaves'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-pur-etale-sum-flat-kflat: the existing statement is 'Etale sum extension preserves flat sheaves and K-flat complexes'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-pur-etale-sum-flat-terms-aux: the existing statement is 'Etale sum extension preserves flat terms'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-pur-etale-sum-kflat-aux: the existing statement is 'Etale sum extension preserves unbounded K-flatness'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-pur-etale-sum-right-adjoint-tensor: the existing statement is 'Sum-evaluation normalization of the etale right-adjoint tensor map'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-pur-etale-sum-tensor-test-projection: the existing statement is 'Projection comparison for arbitrary acyclic tensor tests'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-pur-etale-sum-tensor-test: the existing statement is 'Exactness of transported etale sum extension'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-pur-etale-sum-tensor-totalization: the existing statement is 'Etale sum extension and unbounded total tensor complexes'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-pur-etale-support-map-compatibility: the existing statement is 'Etale proper-support normalization intertwines exchange and projection'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-pur-finite-etale-dualizing-normalization: the existing statement is 'Finite-coefficient etale exceptional normalization and its dualizing comparisons'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-pur-source-etale-derived-projection: the existing statement is 'Source-library derived projection formula for etale sum extension'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-sp-etale-compactification-sheaf-scalar-map: the existing statement is 'Ordinary compactified etale scalar mate on local sheet generators'; the new statement isolates the unit evaluation counit/projection identity on sheaves and unbounded derived objects. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs def-weil-pbc-etale-shriek-base-change-map: the existing statement is 'Base change morphism for etale extension by zero'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-weil-pbc-affine-free-etale-module-eventual-hom-lift: the existing statement is 'Eventual lifting of morphisms from fixed finite affine free families'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-weil-pbc-etale-shriek-base-change-modules: the existing statement is 'Etale extension by zero commutes with base change for module sheaves'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-weil-pbc-inverse-image-free-etale-module: the existing statement is 'Inverse image of the free sheaf of modules j_{W!}Lambda_W on an etale object is the free sheaf on its base change (Stacks 03S6 for the constant sheaf)'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-weil-pbc-modulecat-upperstar-free-yoneda: the existing statement is 'Base change of free Yoneda etale module sheaves (source-library model)'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-weil-pbc-underived-exchange-module-linear: the existing statement is 'The underived exchange morphism is linear on sheaves of modules'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-coef-etale-open-total-tensor: the existing statement is 'Unbounded total tensor projection for etale extension without quasi-compactness'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs sbc-prop-extension-by-zero-and-arbitrary-base-change: the existing statement is 'Extension by zero base change'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs def-asd-compact-support-graph-comparison: the existing statement is 'The specified sheaf and unbounded derived graph comparison'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs def-f7-etale-compactification-graph-map: the existing statement is 'The canonical etale compactification graph map'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs def-pur-etale-horizontal-support-comparisons: the existing statement is 'Canonical etale compact-support, horizontal composition and base-change comparisons'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs def-pur-etale-projection-data: the existing statement is 'Canonical section and stalk comparisons for etale sum projection'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs def-sp-etale-compact-support-normalization: the existing statement is 'Graph-normalized ordinary etale compact-support comparison datum'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-asd-compact-support-finite-graph-isomorphism: the existing statement is 'The specified graph comparison for finite etale morphisms'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-asd-compact-support-graph-coherence: the existing statement is 'Base-change, proper-refinement and identity equations for the graph map'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-asd-compact-support-graph-derived-isomorphism: the existing statement is 'Invertibility of the specified graph map on unbounded complexes'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-asd-compact-support-graph-geometric-base-change: the existing statement is 'The specified forward graph comparison at a geometric base change'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-asd-compact-support-graph-sheaf-normalization-transpose: the existing statement is 'Transpose of graph comparison'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-asd-compact-support-graph-sheaf-normalization: the existing statement is 'Graph comparison agrees with the canonical map into direct image'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-asd-etale-compact-support-normalization: the existing statement is 'Normalization of compactified etale support and its exchange'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-asd-open-projection-exchange: the existing statement is 'Ordinary etale open tensor comparison commutes with base change'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-cbc-base-change-mate-stalk: the existing statement is 'Stalk description of the extension-by-zero base-change morphism'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-cbc-derived-extension-zero-base-change-open-pasting: the existing statement is 'Underived open-immersion pasting for open base change'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-cbc-derived-extension-zero-base-change-underived-compatibility: the existing statement is 'Underived canonical open base-change compatibility'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-cbc-derived-extension-zero-base-change-vertical-pasting: the existing statement is 'Underived vertical pasting for open base change'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-fix-open-base-change-derived-unit: the existing statement is 'The descended finite open exchange retains its original unit transpose'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-fix-open-scalar-exchange: the existing statement is 'Scalar extension respects the open base-change comparison'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-fix-site-open-exchange-sheaf: the existing statement is 'Ordinary sheaf site comparison respects open exchange'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-fix-site-open-exchange: the existing statement is 'Site comparison respects the normalized open base-change map'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-compact-support-graph-tensor-evaluation: the existing statement is 'Tensor evaluation of the normalized compactification graph'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-horizontal-support-mate: the existing statement is 'Etale horizontal compact-support exchange is the composition mate'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-open-scalar-exchange: the existing statement is 'Scalar balancing respects ordinary etale open base change'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-projection-kan-comparison: the existing statement is 'The existing canonical Kan-extension etale projection comparison'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-projection-section-normalization: the existing statement is 'Section normalization of the canonical Kan projection isomorphism'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-projection-stalk-normalization: the existing statement is 'Section formula implies the normalized geometric-stalk square'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-sheaf-projection-map: the existing statement is 'Etale sum-extension sheaf projection formula'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-sum-flat-aux: the existing statement is 'Etale sum extension preserves flat sheaves'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-sum-flat-kflat: the existing statement is 'Etale sum extension preserves flat sheaves and K-flat complexes'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-sum-flat-terms-aux: the existing statement is 'Etale sum extension preserves flat terms'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-sum-kflat-aux: the existing statement is 'Etale sum extension preserves unbounded K-flatness'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-sum-right-adjoint-coherence: the existing statement is 'Coherence of normalized etale sum right adjoints'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-sum-right-adjoint-tensor: the existing statement is 'Sum-evaluation normalization of the etale right-adjoint tensor map'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-sum-tensor-test-projection: the existing statement is 'Projection comparison for arbitrary acyclic tensor tests'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-sum-tensor-test: the existing statement is 'Exactness of transported etale sum extension'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-sum-tensor-totalization: the existing statement is 'Etale sum extension and unbounded total tensor complexes'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-support-map-compatibility: the existing statement is 'Etale proper-support normalization intertwines exchange and projection'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-finite-etale-dualizing-normalization: the existing statement is 'Finite-coefficient etale exceptional normalization and its dualizing comparisons'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-source-etale-derived-projection: the existing statement is 'Source-library derived projection formula for etale sum extension'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-supported-constant-exchange-normalization: the existing statement is 'Canonical closed constant exchange and its underived comparison square'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-sp-etale-compactification-sheaf-scalar-map: the existing statement is 'Ordinary compactified etale scalar mate on local sheet generators'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-amb-etale-left-comparison-base-change: the existing statement is 'Etale compact-support composition comparison commutes with base change'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-etale-normalization-comparison-coherence vs lem-trf-open-square-exchange: the existing statement is 'Open-square exchange from restriction of direct image'; the new statement isolates the arbitrary-K conjugate open comparison and conditional transport of any normalized tensor family, together with refinement equations. Shared source tags alone do not supply that conclusion.

lem-pur-adjoint-projection-tensor-transfer vs lem-pur-adjoint-left-projection-action: the existing node assumes a strong monoidal left adjoint and constructs its projection action; the new node transfers an arbitrary compatible module projection across an isomorphism between two left adjoints and uses a separately assumed unit-evaluation identity.

lem-pur-adjoint-projection-tensor-transfer vs lem-pur-ordered-tensor-coefficient-mate: the existing node compares scalar tensor routes between four categories; the new node transports Hom bijections by d and identifies the projection transpose with a tensor-unit map.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-sum-right-adjoint-coherence: the existing node gives composition of rho and base-change of eta/evaluation at A_X. The new node identifies the all-K chi as the conjugate of open compact-support composition, states the projection restriction, and transports arbitrary normalized tensor families; it is not a special case of the existing coefficient-unit conclusion.

lem-pur-etale-sum-unit-evaluation vs lem-pur-compact-support-graph-tensor-evaluation: the existing node concerns graph evaluation after the proper pullback and a normalized compactification comparison. The new node concerns the sum/restriction counit at the coefficient unit, with no compactification or finiteness hypotheses.

lem-pur-etale-sum-unit-evaluation vs lem-asd-etale-sum-extension-tensor: the existing statement concerns Tensor compatibility for etale sum extension; the new statement concerns unit evaluation for arbitrary commutative rings and schemes, including the ordinary sheaf counit and its derived localization, with the explicit maps and hypotheses written in the node.

lem-pur-etale-sum-unit-evaluation vs lem-pur-co-smooth-etale-locality: the existing statement concerns Source-etale locality, without derived descent; the new statement concerns unit evaluation for arbitrary commutative rings and schemes, including the ordinary sheaf counit and its derived localization, with the explicit maps and hypotheses written in the node.

lem-pur-etale-sum-unit-evaluation vs lem-sp-etale-sum-coefficient-computation: the existing statement concerns Sheetwise flat-complex computation of the compactified etale coefficient arrow; the new statement concerns unit evaluation for arbitrary commutative rings and schemes, including the ordinary sheaf counit and its derived localization, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-per-ind-etale-derived-hom-continuity: the existing statement concerns Derived sections and Hom along affine etale limits; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-per-noetherian-affine-free-presentation: the existing statement concerns Affine free presentations for finite-type constructible modules over Noetherian rings; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-per-noetherian-etale-sum-constructible: the existing statement concerns Constructibility of etale sum-extension with Noetherian coefficients; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-fd-artin-schreier-finite-lisse: the existing statement concerns Artin–Schreier character sheaves over arbitrary finite rings are flat lisse lines; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-fd-base-change: the existing statement concerns Base change of the transform; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-weil-pbc-affine-free-etale-module-arrow-descent: the existing statement concerns Arrows between finite sums of affine etale free module sheaves descend; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-weil-pbc-comparison-direct-image-canonical-mate: the existing statement concerns Canonical derived direct-image comparison is the invertible counit mate; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-weil-pbc-constructible-module-limit-descent: the existing statement concerns A constructible sheaf of $\Lambda$-modules on a limit of qcqs schemes descends to some stage (Stacks 09YU (3), essential surjectivity); the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-weil-pbc-etale-compact-support-base-change-qcqs: the existing statement concerns Arbitrary base change for qcqs etale compact support; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-weil-pbc-etale-free-sheaf-constructible: the existing statement concerns Extension by zero of a finite constant sheaf along a qcqs etale map is constructible; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-weil-pbc-etale-shriek-star-finite-modules: the existing statement concerns Extension by zero equals direct image for finite etale module sheaves; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lemma-weil-pbc-normalization-exact-sequence: the existing statement concerns Normalization comparison exact sequence; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-sf-etale-generic-immersion-projection: the existing statement concerns Projection formula for an immersion extension by zero; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-sf-open-tensor-normalization: the existing statement concerns Open-extension unit normalization for derived tensor and base change; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs cor-cbc-derived-extension-zero-base-change: the existing statement concerns Derived extension-by-zero base change; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs cor-cbc-proper-coincidence: the existing statement concerns Proper morphisms: compact supports equal direct image; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs def-sp-constant-scalar-pullback-comparison: the existing statement concerns Canonical constant-coefficient scalar extension, direct image and pullback comparison; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs def-sp-etale-adjoint-chart-comparison: the existing statement concerns Derived sum adjunction and normalized etale chart left comparison; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs def-sp-fixed-compact-support-comparison: the existing statement concerns Specified compact-support comparison on bounded-below etale representatives; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs det-sp-reduction-exceptional: the existing statement concerns Exceptional inverse image of a smooth morphism commutes with extension of coefficients; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs fix-lem-exchanges: the existing statement concerns Exchange functoriality: naturality, identities, and pasting; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-amb-compact-support-site-comparison-open: the existing statement concerns Bounded compactified site comparison commutes with open restriction; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-amb-shriek-open-exchange-adjoint: the existing statement concerns Open compact-support exchange is the extension-composition mate; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-asd-compact-projection-exchange: the existing statement concerns Compact-support projection maps commute with etale exchange; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-asd-etale-sum-extension-tensor: the existing statement concerns Tensor compatibility for etale sum extension; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-asd-proper-open-refinement-adjoint-projection: the existing statement concerns Adjoint of the unbounded proper-open refinement comparison; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-cbc-extension-zero-base-change: the existing statement concerns Extension by zero commutes with arbitrary base change; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-finrepair-modification-extension-zero: the existing statement concerns Extension by zero under a proper modification; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-co-smooth-etale-locality: the existing statement concerns Source-etale locality, without derived descent; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-compact-scalar-coherence: the existing statement concerns Ordinary etale compact-support scalar compatibility with projection and composition; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-etale-horizontal-double-counit: the existing statement concerns Double-counit identification in an etale-horizontal square; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-scalar-exchange-constituents: the existing statement concerns Finite-ring scalar extension commutes with the specified proper and open exchange constituents; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-pur-supported-hom-pullback: the existing statement concerns Pullback compatibility of the supported-Hom identification; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-sf-class-compact-support-comparison: the existing statement concerns On the coefficient class the compact-support functor is computed on the étale site; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-sp-etale-sum-coefficient-computation: the existing statement concerns Sheetwise flat-complex computation of the compactified etale coefficient arrow; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs prop-asd-smooth-base-change: the existing statement concerns Arbitrary base change for smooth ambient duality; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs def-trf-weil-extension-zero: the existing statement concerns Weil extension by zero; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-trf-compact-composition-tower-formula: the existing statement concerns Computing finite pro-etale compact-support composition on a compatible tower; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-trf-compact-frobenius-transport-composition: the existing statement concerns Composition of compact-support transport along powers of geometric Frobenius; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-trf-constructible-etale-ext-continuity: the existing statement concerns Ext continuity for constructible etale modules in affine inverse limits; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-trf-dnc-generic-local-system-devissage: the existing statement concerns Finite-cover exact sequence for a local system on the complement of a divisor; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-trf-filtered-derived-operation-lifts: the existing statement concerns Filtered lifts of sheaf-derived operations and their canonical adjunction maps; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-trf-gabber-strict-local-torsion-bound: the existing statement concerns Gabber strict-local torsion cohomological bound; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-trf-invariant-closed-basechange-identification: the existing statement concerns Invariant closed support base-change identification; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-normalization-comparison-coherence vs lem-trf-section-exceptional-fibre-coherence: the existing statement concerns Coherence of exceptional fibre comparisons for section families; the new statement concerns the all-K open conjugate and conditional comparison of normalized tensor families, with the explicit maps and hypotheses written in the node.

lem-pur-etale-sum-unit-evaluation vs lem-asd-etale-sum-extension-tensor (hypotheses and normalization): the existing derived reverse-order projection/counit identity assumes a finite coefficient ring and Noetherian schemes. The new statement has arbitrary commutative A and arbitrary schemes, and includes the sheaf identity and termwise localization normalization for the fixed forward-order generator projection. The existing finite/Noetherian theorem is useful for the parent's special setting but does not state the new general sheaf-and-derived assertion. The construction and descent in old Steps 2–3 use neither omitted finiteness condition; this is why the new standalone statement makes both absences explicit.

## Preserved returned proof and exact allocation

### Returned step 1 → lem-pur-adjoint-projection-tensor-transfer

Abbreviate $T=e^*$, $S=S_e$, $F=F_e$, $G=G_e$, $d=d_e$, and write $J_F,J_S$ for the adjunction Hom bijections. Conjugacy applied to the isomorphism $d^{-1}:S\to F$ makes $\rho:G\to T$ a natural isomorphism. The defining mate equation is $\operatorname{ev}_K\circ S(\rho_K)=\varepsilon_K\circ d_{GK}^{-1}$; composing with $d_{GK}$ gives the equation in the statement. Conversely that equation says that each component is the unique $S\dashv T$ transpose of $\varepsilon_K\circ d_{GK}^{-1}$, so it characterizes $\rho$. More generally, for $a:FN\to K$, naturality of $d$ and this equation give
$$J_S(a\circ d_N^{-1})=\rho_K\circ J_F(a).\tag{1}$$
Indeed the inverse transpose of the right side is $\operatorname{ev}_K S(\rho_K)S(J_F(a))=\varepsilon_K F(J_F(a))d_N^{-1}=a d_N^{-1}$.

Cited inputs retained for that future proof: def-weil-pbc-adjunction-conjugate, def-weil-pbc-adjunction-mate.

### Returned step 2 → lem-pur-etale-sum-unit-evaluation

First compute with sheaves. Write $\mathbf1=A_X$, and $u:T\mathbf1\xrightarrow{\sim}A_U$ for the coefficient-unit comparison. For a sheaf $H$ on $X$, put $a_H=\lambda_{TH}\circ(u\otimes1):T\mathbf1\otimes TH\to TH$. The specified sheaf sum projection $p^0$ satisfies
$$\operatorname{ev}^0_H\circ e_{\Sigma!}(a_H)\circ p^0_{T\mathbf1,H}=\lambda_H\circ(\operatorname{ev}^0_{\mathbf1}\otimes1_H).\tag{2}$$
On a lift-indexed tensor generator $(s,b)\otimes h$, both sides give $b h$ in $H(W)$: the first forms $(s,b\otimes s^*h)$ and evaluates that lift, while the second evaluates $(s,b)$ and multiplies by $h$. Here $TH$ on $(W,s)$ is restriction of $H$ to $W$, so the evaluation has this meaning; the restriction identification applies to the underlying abelian sheaf and respects the constant-$A$ action. Equality on finite sums follows by linearity; the universal property of tensor and module sheafification then gives equality of the sheaf maps. This checks maps before sheafification, without identifying all sheaf sections with presheaf sums.

Cited inputs retained for that future proof: lem-pur-etale-sheaf-projection-map, def-weil-pbc-etale-sum-extension, def-weil-presheaf-modules-sheafification, lem-weil-pbc-etale-restriction-injectives, lem-weil-pbc-etale-inverse-image-restriction.

### Returned step 3 → lem-pur-etale-sum-unit-evaluation

Let now $K$ be arbitrary and choose a flat-term K-flat representative $H$. The complex $T\mathbf1$ is the constant coefficient sheaf in degree zero, hence flat and K-flat: tensor with it is the identity. Pullback preserves flat-term K-flat complexes, and so does sum extension; thus $TH$ and $S(T\mathbf1)$ have the flatness needed to compute the two derived tensors in (2). The totalization comparison identifies $p^\Sigma_{T\mathbf1,K}$ with the degreewise generator map of Step 2. The exact sum/restriction adjunction is termwise on the unbounded categories; its counit is the termwise evaluation, as follows by applying the termwise adjunction and localization to its unit, counit and triangles. Consequently (2) is an equality of maps of total complexes: its unit factor has degree zero, and both sides send the degree-$q$ tensor to $b h$ with differential $b\,d_Hh$. Tensor descent and faithfulness of precomposition with localization extend the equality from these representatives, naturally in $K$. We obtain
$$\operatorname{ev}_K S(a_K)p^\Sigma_{T\mathbf1,K}=\lambda_K(\operatorname{ev}_{\mathbf1}\otimes1_K),\quad a_K=\lambda_{TK}(u\otimes1).\tag{3}$$

Cited inputs retained for that future proof: lem-pc-kflat-resolution, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-pur-etale-sum-flat-kflat, lem-pur-etale-sum-tensor-totalization, lem-amb-etale-adjoint-locality, lem-weil-pbc-termwise-adjunction-homotopy, lem-weil-pbc-site-derived-tensor-descent, lem-weil-pbc-localization-universal-property.

### Returned step 4 → lem-pur-adjoint-projection-tensor-transfer

Put $W=G\mathbf1$, $N=TK\otimes W$, and let $q_F:FN\to K$ be the displayed inverse transpose defining $\tau_K$. The proper-support/projection compatibility gives
$$d_{W\otimes TK}P_{W,K}=p^\Sigma_{W,K}(d_W\otimes1_K).$$
Use this identity to replace $P_{W,K}^{-1}$, and use naturality $F(\mathrm{sym})d_N^{-1}=d_{W\otimes TK}^{-1}S(\mathrm{sym})$. The result is the following equality of maps $SN\to K$:
$$q_Fd_N^{-1}=\lambda_K((\varepsilon_{\mathbf1}d_W^{-1})\otimes1_K)(p^\Sigma_{W,K})^{-1}S(\mathrm{sym}).\tag{4}$$
In particular this uses precisely the specified compactification projection, not an independently chosen projection isomorphism.

Cited inputs retained for that future proof: lem-pur-etale-support-map-compatibility, lem-kun-tensor-sym.

### Returned step 5 → lem-pur-adjoint-projection-tensor-transfer

By Step 1 at $\mathbf1$, $\varepsilon_{\mathbf1}d_W^{-1}=\operatorname{ev}_{\mathbf1}S(\rho_{\mathbf1})$. Naturality of $p^\Sigma$ in its first variable gives
$$(S(\rho_{\mathbf1})\otimes1)(p^\Sigma_{W,K})^{-1}=(p^\Sigma_{T\mathbf1,K})^{-1}S(\rho_{\mathbf1}\otimes1).$$
Substitute both equations into (4), then use (3) followed by cancellation of $p^\Sigma_{T\mathbf1,K}$. We obtain
$$q_Fd_N^{-1}=\operatorname{ev}_K S(a_K\circ(\rho_{\mathbf1}\otimes1)\circ\mathrm{sym}).\tag{5}$$
Since $\eta=u\rho_{\mathbf1}$, the arrow inside $S$ is $\lambda_{TK}(\eta\otimes1)\mathrm{sym}=\operatorname{unitor}_{TK}(1\otimes\eta)$. The last equality is naturality of the signed symmetry and its unit constraint; it does not discard a Koszul sign. All maps have degree zero and the coefficient unit is in degree zero.

Cited inputs retained for that future proof: .

### Returned step 6 → lem-pur-adjoint-projection-tensor-transfer

Apply $J_S$ to (5). The right side transposes to $\operatorname{unitor}_{TK}(1\otimes\eta)$, by the inverse-transpose formula. By (1) and the definition $J_F(q_F)=\tau_K$, the left side transposes to $\rho_K\tau_K$. This proves the required equality. Every ingredient used above is natural in $K$, so the equality is one of derived natural transformations. In particular, this argument compares actual maps in the derived category; it never deduces equality of derived morphisms from equality of their stalk cohomology maps.

Cited inputs retained for that future proof: def-weil-pbc-adjunction-mate.

### Returned step 7 → lem-pur-etale-normalization-comparison-coherence

For a refinement or comparison of compactifications let $t:F^c\xrightarrow{\sim}F^{c'}$ be its canonical left comparison. The quasi-finite comparison gives $d^{c'}t=d^c$, and the support-map compatibility says that $t$ also intertwines the specified projections. Define the right comparison $r:G^c\xrightarrow{\sim}G^{c'}$ by conjugacy of $t^{-1}$. Its counit equation and $d^{c'}t=d^c$ show, by the uniqueness in Step 1, that $\rho^{c'}r=\rho^c$. At $\mathbf1$ this gives $\eta^{c'}r_{\mathbf1}=\eta^c$. Substitution in the inverse-transpose formula, using the projection compatibility, gives $r_K\tau^c_K=\tau^{c'}_K(1\otimes r_{\mathbf1})$. These formulas prove independence under the canonical comparisons. They agree through a common refinement because left comparisons satisfy their cocycle, and conjugacy respects composition.

Cited inputs retained for that future proof: lem-sfb-quasifinite-compact-support-exact, lem-pur-etale-support-map-compatibility, def-weil-pbc-adjunction-conjugate.

### Returned step 8 → lem-pur-etale-normalization-comparison-coherence

Let $g:X'\hookrightarrow X$ be open and $U'=U\times_XX'$ with open projection $h:U'\hookrightarrow U$ and etale projection $e':U'\to X'$. On an etale test object over $X'$, lifts to $U'$ correspond bijectively to lifts to $U$, by the fibre-product property. Hence restriction of the sum/evaluation counit and the generator map in (2) is exactly the corresponding counit and generator map for $e'$. The compact-support exchange identifies the restriction of $d_e$ with $d_{e'}$ by clause (1) of support-map compatibility. To specify the right comparison, use
$$\chi_K=(\rho_{e',g^*K})^{-1}\circ(h^*e^*K\cong e'^*g^*K)\circ h^*\rho_{e,K}:h^*G_eK\xrightarrow{\sim}G_{e'}g^*K.$$
This is the canonical right-adjoint restriction comparison: the left composites $F_eD(h_{\Sigma!})$ and $D(g_{\Sigma!})F_{e'}$ compare by compact-support composition for $eh=ge'$. Under $d$ their comparison is the nested-summand identification for sum extension. Conjugating this equality, the mate-pasting rule gives the displayed formula for $\chi$, since the right adjoints of the two open sum extensions are $h^*,g^*$.

Cited inputs retained for that future proof: def-pc-fibre-product, lem-weil-pbc-etale-shriek-base-change-modules, lem-pur-etale-support-map-compatibility, lem-sfb-quasifinite-compact-support-exact, lem-amb-etale-adjoint-locality, lem-weil-pbc-mate-pasting.

### Returned step 9 → lem-pur-etale-normalization-comparison-coherence

The unit comparison identifies $h^*\eta_e$ with $\eta_{e'}\chi_{A_X}$ under $g^*A_X=A_{X'}$. Pulling back the equality of Step 6 along $h$ and using $h^*e^*=e'^*g^*$ therefore gives
$$\rho_{e',g^*K}\chi_K h^*\tau_{e,K}=\operatorname{unitor}(1\otimes\eta_{e'}\chi_{A_X}).$$
The already proved equality for $e'$ makes the right side $\rho_{e',g^*K}\tau_{e',g^*K}(1\otimes\chi_{A_X})$. Cancel the isomorphism $\rho_{e',g^*K}$ to obtain the tensor-map restriction identity. The restrictions of the projection normalization agree because their generator maps agree on every test object as checked in Step 8, and the compactification comparison intertwines them. This proves the last assertion, including the specified maps.

Cited inputs retained for that future proof: .

## Unfinished work

The three new nodes are deliberately statement-only, as the return directs; their future splits/proofs are not claimed complete. This delivery completes the assigned one-level re-split. The required server dry run and push are reported by the delivery tool.
