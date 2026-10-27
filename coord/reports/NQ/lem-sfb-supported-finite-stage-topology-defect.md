# Worker report: lem-sfb-supported-finite-stage-topology-defect

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-supported-finite-stage-topology-defect.json`: item, statement unchanged verbatim; four assembly steps, 2332 characters of proof text.
- `dag/nodes/sec-six-functors-basics/lem-sfb-supported-common-field-scalar-models.json`: new statement, unsplit, no Mathlib match. Carries returned steps 1–4: common-field models, support/scalar comparisons, module-model transport and normalization of all units.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-model-topology-derived-hom.json`: new statement, unsplit, no Mathlib match. Carries returned steps 5–6: constructibility and continuity of internal Hom, the two evaluation comparisons, derived sections and equality of the actual scalar map.
- `report.md`, `citations.json`, and the search command's `searches.jsonl` are the delivery evidence. `returned-proof.json` retains the eight returned steps verbatim locally; they are also reproduced below in this report. Local scripts only construct the sandbox files and are not project modifications.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, supported finite-stage/topology notions and theorem name. No project declaration there states the item. The existing statement `AlgebraicGeometry.ProEtale.supported_finiteStage_topology_defect` in `lean/Sheaf/Paper/SupportedFiniteStageTopologyDefect.lean:214` ends in `sorry`; it is not an attachment. Its supported objects, independent fields and immersions, ranks, actual derived unit and arbitrary distinguished triangle agree with the item. No Lean was written or compiled.

## Literature wanted

WANTED: a precise literature proof of the norm algebraic-closure internal-Hom and global cohomology topology comparisons, for the existing obligations `lem-sfb-norm-algcl-internal-hom-base-change` and `lem-sfb-norm-algcl-cohomology-topology-comparison`, used by `lem-sfb-finite-model-topology-derived-hom`. These were already explicitly wanted in the reviewed delivery; this repair preserves that open mathematical work and does not present it as HRS Lemma 7.9.

WANTED: a single exact literature reference for the assembled normalization statements of `lem-sfb-supported-common-field-scalar-models` and `lem-sfb-finite-model-topology-derived-hom`. Their source is the agent argument below the current blueprint paragraph (3), extracted from the reviewed eight-step item proof, rather than a claim that the blueprint or a Stacks tag states the entire new lemma. The component inputs are already cited DAG nodes, with their exact source places retained below.

## Return repaired

The human's 2026-10-21 re-split request required at least two comparable, independently usable statement-only obligations and an assembly proof of at most 3000 characters. The sandbox initially contained only dispatcher markers, with no node files, report or search log. The first dry run therefore reported no node files. I copied the current shared node, including its reviewed repairs, citations, searches, blueprint lineage and Lean records. I did not restore an obsolete version or discard any retained search results.

Returned steps 1–4 (3446 characters) now belong to `lem-sfb-supported-common-field-scalar-models`; steps 5–6 (2485 characters) belong to `lem-sfb-finite-model-topology-derived-hom`. These are distinct arguments: construction and normalization of supported finite-field models versus comparison of derived global Hom for arbitrary finite-field constructible inputs. The new nodes are comparable in size and neither states cone orthogonality or hides the whole item. Steps 7–8 remain verbatim in the parent, following two short applications of the new nodes. The parent statement, coefficient topologies, ordinary unbounded category, actual unit and all edge cases remain exactly as reviewed.

Each new node has `proof: []`, `proof_deps: []`, `proof_origin: null`, `status: unsplit`; future workers prove them. The complete arguments assigned to them, without shortening or blurring, appear below. The existing two norm-coefficient obligations are reused, not recreated. The derived-Hom node states an isomorphism of derived global Hom objects; the parent takes cohomology using the existing sections-model node, rather than introducing redundant degreewise leaves.

## Searches and blueprint lineage

I searched all `dag/nodes/` and the whole blueprint with `tools/blueprint_refs.py search`, using `finite-stage`, `common coefficient`, `internal Hom`, `topology comparison`, `scalar extension`, `common finite coefficient field` and `evaluation-transpose`; I inspected the close candidates listed under Not duplicates. Searches of project Lean found no finished version of either new statement. The ancestor command returns `None`: this item is an agent obligation absent from the blueprint. Both children inherit that null ancestor and prepend this item to the existing via list; their precise from.place identifies paragraph (3) and the returned steps they take over. No unit or chapter record was changed; this item is not its unit's key statement.

For each new node I ran LeanFinder twice with distinct formulations, Loogle, grep through Mathlib, and LeanSearch through the required `msearch.py` command. Each node records its own five exact query strings and the command's original result records. Both LeanSearch calls were unavailable (rate limit), and both are marked `unavailable`. No query or result was invented. The item's ten historical searches are retained untouched.

For the models node the second LeanFinder search found `ModuleCat.homEquiv_extendScalarsComp`, inspected at Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:992, and scheme-module `restrictAdjunction`/`restrictFunctorAdjCounitIso`, inspected at Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:416 and :425. These are ordinary scalar-composition or structure-sheaf open-restriction facts, not the full ordinary-unbounded condensed supported-model lemma. The other hits concern existence of sheafification, light condensed closed structure or affine transition limits.

For the derived-Hom node the second search found `LightCondensed.ihomPoints`, `ihom_map_val_app` and `ihomPoints_symm_comp`, inspected at Mathlib/Condensed/Light/InternallyProjective.lean:53, :72, :83. They concern underived internal Hom over a fixed ring on light profinite sets, not constructible pro-etale derived Hom for the two rings C and B. The grep hits at Mathlib/Condensed/TopCatAdjunction.lean:217–218 state full faithfulness of compactly generated spaces into condensed sets, which is a different functor. The Loogle hits are general derived localization identities. None is an exact match or one-line specialization of a new node. Both new nodes remain unsplit, with zero Mathlib leaves.

## Not duplicates

lem-sfb-supported-common-field-scalar-models vs lem-sfb-coefficient-heart-lisse-extension-constructible: the existing lemma gives only constructibility of a fixed-coefficient supported lisse module; the new lemma constructs common-field derived models and normalized comparisons across supports and C/B coefficients.

lem-sfb-supported-common-field-scalar-models vs det-lem-coefficient-finite-descent-lisse: finite descent and underived Hom for lisse C-coefficients do not give support/scalar commutation or normalization for the independent finite-field supported inputs and B-coefficients.

lem-sfb-supported-common-field-scalar-models vs lem-sfb-closed-supported-scalar-comparison: the existing statement is the closed-support comparison conditional on unbounded localization data; the new statement verifies those data in the finite-stage setting and combines open factors, finite-field models and unit reassociation.

lem-sfb-supported-common-field-scalar-models vs lem-sfb-locally-closed-generator-tensor-intersection: the existing lemma tensors two same-ring supported generators over their scheme-theoretic intersection; it does not change coefficient rings or identify scalar units.

lem-sfb-supported-common-field-scalar-models vs lem-sfb-continuous-qbar-constructible-generators: the latter is a finite-cone generation theorem for all-continuous coefficients and explicitly imposes no common finite field. The new node starts with two given finite coefficient models and does not claim finite descent for arbitrary B-lisse modules.

lem-sfb-finite-model-topology-derived-hom vs lem-sfb-norm-algcl-internal-hom-base-change: the existing result gives only the B-side local internal-Hom comparison, explicitly without global-section comparison. The new lemma assembles both topologies with constructibility, continuity, global sections and actual-map compatibility; it reuses this result in its assigned argument.

lem-sfb-finite-model-topology-derived-hom vs lem-sfb-norm-algcl-cohomology-topology-comparison: the existing statement compares RΓ of scalar-extended V, not derived global Hom or its actual scalar-extension map. The new statement must establish that the relevant V is RHom(K,N) and compare its evaluations on both sides.

lem-sfb-finite-model-topology-derived-hom vs lem-sfb-qlbar-internal-hom-coefficient-comparison: the latter treats C only under a continuity hypothesis; the new lemma verifies that hypothesis and compares C with B on derived global Hom.

lem-sfb-finite-model-topology-derived-hom vs lem-sfb-derived-internal-hom-sections-model: the latter identifies derived sections of a right adjoint with the global Hom complex for a single ring; it does not compare coefficient topologies or prove scalar extension induces an isomorphism.

Both new nodes vs lem-sfb-supported-finite-stage-topology-defect: neither asserts Hom into the cone of the scalar unit vanishes. The first does no Hom topology comparison; the second assumes finite-field constructible models and contains no supported-generator construction or triangle conclusion. The parent still has to combine them, take cohomology, compute the actual adjunct and use the exact Hom sequence.

## Review by NQ

I read the current chapter and unit records, SETUP's three levels, GOAL, stage-1 contract and delivery-errors B–E. I read the current blueprint `main-20261015/.../sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3), and the reviewed eight-step proof of this item. Paragraph (3) supplies the direct-image stability context, not a proof that the two coefficient rings agree. The new nodes are explicitly agent obligations. For the generic final assembly I also read Stacks `sites-cohomology.tex` Tag 07A6 (`lemma-adjoint`), Section 08J7 (`section-internal-hom`), Lemmas 08JA (`lemma-section-RHom-over-U`) and 08J9 (`lemma-internal-hom`), and `derived.tex` Tags 0146 (`lemma-composition-zero`) and 0149 (`lemma-representable-homological`). The direct statements of all 24 originally cited nodes were opened and checked, not just their titles or proofs.

The models statement introduces every field, topology, module, support, derived functor and comparison independently of the parent. Its A_E uses the restricted norm topology; C requires values in a finite subextension, whereas B allows every continuous map into the uncompleted algebraic closure. E0 is the compositum, not an identification E=F. It asserts bounded constructibility of K,N over the finite field only; it does not assert that arbitrary B-extensions are bounded. It retains linearity and the open-unit/closed-counit normalization. In the assigned steps, module equivalence and the separate scalar-adjunction transport supply the actual unit; finite-type-over-Noetherian and Noetherian-open ensure the support comparisons have quasi-compact complements. For closed strata the quotient-ring ascending-chain argument gives the missing Noetherian check. The finite-field flatness node supplies exactness for L0,M0; pullback comparison checks their lissity on the original trivializing covers. Open tensor normalization and the closed-supported comparison are different inputs, and the exact unbounded-calculus hypotheses are verified from the degree-zero recollement sequence before use. These are real tasks preserved below, not unsupported assertions derived from a definition.

For the derived-Hom statement I checked its K,N are finite constant-model bounded constructible over a finite E and hence N is bounded below. The predicate-comparison node, which the earlier maintainer added, is retained in the assigned argument: dc-hom-preserves uses the stratified local-finite-presentation predicate, so one must compare both before and after applying it. Continuity supplies exactly the hypothesis of the C-side internal-Hom comparison. The B-side is a distinct input and is not deduced by treating B as the filtered colimit C. The global topology node applies to D only after D is known bounded constructible. Equality of the actual map is retained as equality of evaluation transposes on the derived objects; restriction of coefficients in RΓ is also retained explicitly. No site-perfectness, Ω completeness, flatness of c or finite global cohomological-dimension hypothesis has been added.

New parent step 1 uses precisely the models node's K,N, four natural isomorphisms and unit compatibility; its statement gives all of them. Step 2 uses precisely the derived-Hom node's isomorphism of actual derived global Hom maps, and the existing sections-model statement's formula H^n RΓ RHom(K,M)=Hom(K,M[n]) for every integer n. Step 3 is returned step 7 verbatim: the normalized coefficient-adjunction statement gives exact restriction, derived adjunction, actual unit and no flatness requirement; naturality makes the adjunct U(Ju)∘η_G equal η_H[n]∘u. Step 4 is returned step 8 verbatim: Hom-into-triangle-exact gives zero consecutive composites and exactness, and the triangulated-category definition supplies shifts and rotations, so injectivity in degree n+1 kills the boundary and surjectivity in degree n kills q. The arithmetic, functor substitution and taking cohomology of an isomorphism are elementary within these cited applications. Every non-elementary input has a node, and citations.json contains literal statement extracts for every citation in all four steps.

I checked empty S or T, zero rank, E=F, either field contained in the other, two genuinely different finite fields, identical supports and distinct supports. Zero objects remain zero under support and derived extension; there is no positive-rank or nonempty-cover inference. If E=F the compositum and finite-field extension reduce to the identity. On a geometric point with free finite-rank models, both coefficient rings have the same point value Ω and the normalization is the usual balanced-tensor unit. With K=0 or N=0, all internal Hom comparisons and the scalar map are zero-object isomorphisms. Shifts are allowed in all integer degrees, and the triangle argument uses no chosen cone. These checks found no new statement error; no STATEMENT-DISPUTED change is made.

I checked the long-step requirement: the parent has no step over 2000 characters and its full proof is below 3000. The two new nodes do not depend on each other or on the parent, only on the notions used in their statements. Their original non-elementary arguments, now work for other workers, are retained verbatim below with the original citations. The remaining four off-unit generic tools are inherited declared tool uses (derived sections model, coefficient adjunction, Hom exactness and triangulated axioms); no six-functor route or target statement changed. The earlier review's general concern about topology-comparison ancestry is not resolved by this workload split; the same two WANTED structural inputs remain explicit.

## Complete returned arguments assigned to the new nodes

The following text is the exact returned proof, not a shortened replacement. Sections for new nodes are work briefs, not proof steps inserted into their statement-only JSON.

### lem-sfb-supported-common-field-scalar-models: returned steps 1–4

Returned step 1:

Pass to the small-site section-ring model using [lem-pd-module-ringed-topos-derived-comparison] and [lem-sfb-internal-section-scalar-adjunction]. The first identifies the specified derived tensors and exact open extension; closed internal Homs are identified by uniqueness of their right adjunctions. The second identifies scalar extension/restriction AND their actual units, including $v\mapsto1\otimes v$; thus this passage does not change the triangle in the assertion. A field is Noetherian (its only ideals are zero and itself); hence $X$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. Every open in $X$ is quasi-compact by [lem-weil-pbc-noetherian-open-subscheme-noetherian]. Closed subschemes are Noetherian too: on a Noetherian affine their rings are quotients, whose ascending chains of ideals lift to chains of ideals upstairs, and closed subsets of a Noetherian space are quasi-compact. These observations apply also to the closures used to define $a_!,b_!$.

Cited node statements: lem-pd-module-ringed-topos-derived-comparison, lem-sfb-internal-section-scalar-adjunction, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-open-subscheme-noetherian.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), agent topology-comparison argument; module models and quasi-compactness checks.

Returned step 2:

Take the finite compositum $E_0=EF\subset\Omega$ by [det-def-sfb-qlbar-condensed-subextensions], and write $A_V=A_{E_0,V}$. Extend $L,M$ on their respective supports to $L_0=A_S\otimes_{A_{E,S}}L$ and $M_0=A_T\otimes_{A_{F,T}}M$. These are ordinary degree-zero modules: finite-field scalar extension is exact by [lem-sfb-subfield-flat]. They are lisse: pull back to the covers trivializing $L,M$; [lem-sfb-kflat-scalar-comparison-normalization] identifies the pullbacks of these tensors with the tensors of the pullbacks, hence with $A^r,A^s$. Define $K=(a_!L_0)[0]$, $N=(b_!M_0)[0]$ in $D(A_X)$. They are bounded constructible by [lem-sfb-coefficient-heart-lisse-extension-constructible], since $X$ is Noetherian. The two supports and ranks have not been identified.

Cited node statements: det-def-sfb-qlbar-condensed-subextensions, lem-sfb-subfield-flat, lem-sfb-kflat-scalar-comparison-normalization, lem-sfb-coefficient-heart-lisse-extension-constructible.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), agent topology-comparison argument; one common finite coefficient field; finite models.

Returned step 3:

Scalar extension along each coefficient map used here commutes with $a_!$ and $b_!$. For their open factors this is [lem-sf-open-tensor-normalization], with the identity geometric map and the given change of rings. For the closed factors use [lem-sfb-closed-supported-scalar-comparison] with inverse-image comparisons [lem-sfb-kflat-scalar-comparison-normalization]. Its unbounded-calculus hypothesis follows from [lem-weil-pbc-condensed-open-closed-recollement] and [lem-sfb-exact-open-closed-unbounded-calculus]: all four sheaf functors are exact; the open unit and closed counit are isomorphisms; the mixed restrictions are zero by extension by zero and disjoint supports. Applying the first recollement triangle to a degree-zero sheaf gives the required short exact sequence $0\to j_!j^*M\to M\to i_*i^*M\to0$. Complements are quasi-compact by step 1. Thus the cited unbounded calculus applies, without assuming that the scalar extensions are bounded or flat. The resulting closed comparison is linear over the new coefficient ring, with the precise counit normalization of that node.

Cited node statements: lem-sf-open-tensor-normalization, lem-sfb-closed-supported-scalar-comparison, lem-sfb-kflat-scalar-comparison-normalization, lem-weil-pbc-condensed-open-closed-recollement, lem-sfb-exact-open-closed-unbounded-calculus.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), agent topology-comparison argument; normalized scalar extension across supports.

Returned step 4:

For $R=C_X,B_X$ put $S_R(V)=R\otimes_{A_X}^L V$. Apply step 3 first to $E\to E_0\to C$ on $S$, and to $F\to E_0\to C$ on $T$. The scalar reassociations of [lem-sfb-successive-derived-quotient-normalization] give $G\simeq S_CK$, $H\simeq S_CN$. Applying the same reassociation to $A_X\to C_X\to B_X$ gives $J_XG\simeq S_BK$, $J_XH\simeq S_BN$. All identifications are natural, and the cited reassociation takes successive scalar units to the direct unit, by $(v\otimes z)\otimes w\mapsto v\otimes c(z)w$. We may therefore make these identifications when computing the actual scalar-extension map on morphisms.

Cited node statements: lem-sfb-successive-derived-quotient-normalization.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), agent topology-comparison argument; identify the supported objects and their scalar units.

### lem-sfb-finite-model-topology-derived-hom: returned steps 5–6

Returned step 5:

Put $D=R\mathcal Hom_{A_X}(K,N)$. The predicate comparison [lem-sfb-adic-constructibility-predicate-comparison] for the field $E_0$ on the Noetherian $X$ shows that $K,N$ are bounded constructible in the stratified local-finite-presentation sense. So $D$ is bounded constructible in that sense by [lem-sfb-dc-hom-preserves], applied to $E_0$ in the standing setting. By the same comparison $D$ also has finite constant local models. The complex $K$ has the internal filtered-colimit continuity property of [lem-sfb-constructible-internal-hom-continuity]: $X$ is Noetherian and $K$ has the finite constant local model from step 2. Since $N$ is degree zero, it is bounded below. Consequently [lem-sfb-qlbar-internal-hom-coefficient-comparison] gives the evaluation-transpose isomorphism $\phi_C:S_CD\simeq R\mathcal Hom_{C_X}(S_CK,S_CN)$. Independently, [lem-sfb-norm-algcl-internal-hom-base-change] gives the evaluation-transpose isomorphism $\phi_B:S_BD\simeq R\mathcal Hom_{B_X}(S_BK,S_BN)$. This second input is about the norm coefficient ring, so it is not inferred from the colimit-coefficient result.

Cited node statements: lem-sfb-adic-constructibility-predicate-comparison, lem-sfb-dc-hom-preserves, lem-sfb-constructible-internal-hom-continuity, lem-sfb-qlbar-internal-hom-coefficient-comparison, lem-sfb-norm-algcl-internal-hom-base-change.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), agent topology-comparison argument; internal-Hom comparisons, with each coefficient topology distinguished.

Returned step 6:

Apply [lem-sfb-norm-algcl-cohomology-topology-comparison] to the bounded constructible $A_X$-complex $D$ from step 5. It makes the actual map $R\Gamma(m_D):R\Gamma(S_CD)\to R\Gamma(S_BD)$ invertible. Under $\phi_C,\phi_B$ this is the morphism on derived global Hom induced by $J_X$. Indeed both evaluation transposes are scalar extension of the same evaluation $D\otimes_{A_X}^L K\to N$. Reassociating balanced tensors, their evaluations after $c_X$ agree: both are $B_X\otimes_{A_X}^L(D\otimes_{A_X}^L K)\xrightarrow{1\otimes\mathrm{ev}}S_BN$. The defining tensor/internal-Hom adjunction [sk-def-sfb-derived-tensor-hom] makes the transpose unique. Thus this equality identifies the actual map, including its naturality in arrows, rather than merely identifying its endpoints. Derived global sections of a $C_X$- or $B_X$-complex agree with those of its restriction to $A_X$: by [lem-pur-sheaf-ring-derived-coefficient-adjunction] applied to $A_X\to R$ and the unit $R$ itself, $\operatorname{Hom}_{D(R)}(R,M[n])=\operatorname{Hom}_{D(A_X)}(A_X,M[n])$. Taking degree-$n$ cohomology and using [lem-sfb-derived-internal-hom-sections-model] yields a bijection $u\mapsto J_Xu$ from $\operatorname{Hom}_{D(C_X)}(G,H[n])$ to $\operatorname{Hom}_{D(B_X)}(J_XG,J_XH[n])$ for every integer $n$. The module equivalences in step 1 preserve these constructions and underlying abelian sheaves.

Cited node statements: lem-sfb-norm-algcl-cohomology-topology-comparison, sk-def-sfb-derived-tensor-hom, lem-sfb-derived-internal-hom-sections-model, lem-pur-sheaf-ring-derived-coefficient-adjunction.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), agent topology-comparison argument; global comparison and evaluation identify its actual map.

### Parent: retained returned steps 7–8

Returned step 7:

Use [lem-pur-sheaf-ring-derived-coefficient-adjunction] for $c_X:C_X\to B_X$. The right adjoint is exact restriction, and the normalized derived unit is exactly the one in the statement. The adjunction sends $J_Xu:J_XG\to J_XH[n]$ to $U_XJ_Xu\circ\eta_G=\eta_{H[n]}\circ u$ by naturality of the unit. Since these exact derived functors and their units commute with shifts, this is $\eta_H[n]\circ u$. Composing with the bijections from step 6 therefore shows that the maps $\operatorname{Hom}(G,H[n])\xrightarrow{\eta_H[n]\circ-}\operatorname{Hom}(G,U_XJ_XH[n])$ are bijections for all integers $n$. This step uses no flatness of $c_X$.

Cited node statements: lem-pur-sheaf-ring-derived-coefficient-adjunction.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), agent topology-comparison argument; adjunction transfers the comparison to the specified unit.

Returned step 8:

Let the triangle in the assertion be arbitrary and let $q:G\to Q_H[n]$. By [lem-weil-pbc-hom-into-triangle-exact] applied also to the shifted and rotated distinguished triangles [def-weil-triangulated-category], its boundary $dq:G\to H[n+1]$ is killed by $\eta_H[n+1]$. Step 7 makes that map on Hom injective, so $dq=0$. Exactness at $Q_H[n]$ gives $q=vh$ for some $h:G\to U_XJ_XH[n]$. Surjectivity in step 7 writes $h=\eta_H[n]u$; consecutive triangle arrows compose to zero, so $q=v\eta_H[n]u=0$. Thus every element of the asserted Hom group is zero. Nothing depended on a chosen cone, a nonempty support, a positive rank, or a relation between $S,T$ or $E,F$, so the asserted edge cases are included.

Cited node statements: lem-weil-pbc-hom-into-triangle-exact, def-weil-triangulated-category.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), agent topology-comparison argument; exact Hom sequence; arbitrary cones and edge cases.

## What was not finished

The two new obligations are intentionally unsplit, as the return explicitly requires. Their future workers have the original argument above, the current statement and the prior component nodes. This delivery performs only the requested stage-1 workload split. No Lean proof, compiler, Lake or build operation is part of it.

## Validation

The server-only preliminary review_split accepted the parent assembly. Final deliver.py dry-run and push results are recorded after their completion.
