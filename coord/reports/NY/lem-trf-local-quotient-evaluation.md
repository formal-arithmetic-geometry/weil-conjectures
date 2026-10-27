# Stage-1 delivery: lem-trf-local-quotient-evaluation

## Files written

- dag/nodes/sec-trace-formula/lem-trf-local-quotient-evaluation.json — item, split into six proof steps; statement and its statement dependencies retained.
- dag/nodes/sec-trace-formula/lem-trf-immersion-over-separated-base.json — statement, Mathlib leaf: an immersion followed by a separated morphism is separated, by the composition instance with the immersion's separatedness inferred.
- citations.json — fourteen verbatim statement quotations, one for each step/node citation.
- searches.jsonl — actual search-command records; the item's prior Mathlib searches are retained in its JSON.

## Attachments

None. Searches by the exact blueprint tag and by local quotient/evaluation and very-ampleness notions in lean/WeilConjectures found no declaration giving the whole item. The project's Modules/VeryAmple.lean uses finite-dimensional projective-space embeddings and does not state this arbitrary quasi-coherent local quotient theorem. There was no earlier split or report in this sandbox.

## WANTED

None. The necessary Stacks sources and Mathlib files are present locally.

## What was wrong or incomplete

The item had no proof. Its statement agrees with the initial part of Stacks 01VR, (2) implies (4); there is no statement dispute. This item stops before proving the resulting classifying morphism is an immersion, and its proof does not assume that later result. I made no statement, hypothesis, or route changes. In particular, an immersion is not required to be closed, the base and its covering need not be quasi-compact, and no finite-type or local-freeness hypothesis on E_j was added.

The only new node is a general scheme-theoretic Mathlib leaf. It does not repackage an evaluation, quasi-coherence, or classifying-morphism clause of the item. The sectionwise direct-image identification, the adjunction formula, and cancellation of a surjective composite are written as elementary arguments in the item rather than made into new nodes.

## Unfinished work

None at stage 1. No Lean was written and no compiler, Lake, or build tool was run.

## Not duplicates

The whole DAG was searched by the source label lemma-subscheme-of-separated-scheme and tag 01L8; neither occurs in an existing node. Blueprint searches for 01L8, 01L7, 01KU, locally closed subscheme, projective bundle, separated is local, and immersion/separated found no blueprint statement of the new leaf. A statement-only scan of the whole DAG also checked separatedness locality and immersion/composition formulations. The new leaf was searched in lean/WeilConjectures by the same notions; there is no corresponding project theorem to attach.

lem-trf-immersion-over-separated-base vs lem-sfb-separated-lfp-target-open-locality: the latter gives target locality and local finite presentation, not separatedness of an immersion followed by a separated morphism; it is cited separately for gluing separatedness.

lem-trf-immersion-over-separated-base vs lem-a1-space-separated-lqf-permanence: the latter assumes a separated locally quasi-finite algebraic-space morphism and proves base-change/open-restriction results; it does not give the general scheme immersion/composition statement without a local quasi-finiteness hypothesis.

lem-trf-immersion-over-separated-base vs lem-trf-affine-square-monomorphism-absolute-separated: the latter starts with a monomorphism into the relative square of a fixed affine scheme and concludes absolute separatedness, rather than arbitrary immersions into arbitrary separated S-schemes.

lem-trf-immersion-over-separated-base vs lem-pc-separated-quasi-separated: the latter takes separatedness as a hypothesis and concludes quasi-separatedness; it is cited separately.

## Review by NY

I read literature/stacks-project/morphisms.tex at lemma-relatively-very-ample-separated (01VQ) and the full (2) implies (4) paragraph of lemma-relatively-very-ample (01VR). The split follows its separatedness, adjoint quotient, evaluation, and projective-quotient sequence. I also read schemes.tex at lemma-subscheme-of-separated-scheme (01L8), its proof, lemma-immersions-monomorphisms, lemma-separated-permanence, and lemma-push-forward-quasi-coherent (01LC). The chapter and sk-i-curve-zero unit were read; this remains an auxiliary projectivity argument on the item's recorded ancestry, not a change of their route. The current blueprint_update of the ancestor was inspected; none of its trace-locality statements is invoked as a projectivity lemma.

For Step 1, I opened the statement of lem-trf-projective-bundle-quotient-geometry and verified its explicit separatedness assertion allows any quasi-coherent E_j, with no finite-type assumption. The new leaf applies with Z=Z_j, P=P(E_j), S=V_j and the hypothesized immersion. I opened lem-sfb-separated-lfp-target-open-locality and checked that its separatedness iff applies to an arbitrary set-indexed cover with no quasi-compactness assumptions. This is the missing gluing tool, and is reused rather than recreated.

For Step 2, lem-pc-separated-quasi-separated says precisely that the diagonal becomes quasi-compact. The definition def-sc-invertible-module explicitly includes quasi-coherence. The statement of pqf-lem-pushforward-qcoh has exactly the two morphism hypotheses now available: quasi-compactness is given and quasi-separatedness was just proved. Its quasi-coherent-module conclusion is sufficient; no coherent-direct-image theorem or properness is being smuggled in. I checked the direct-image section formula in lem-pc-module-pullback-adjunction. This off-unit pushforward result is recorded as a generic tool use in split_report.

For Step 3, the geometry node supplies the actual tautological surjection. The first clause of lem-weil-pbc-module-pullback-epi-direct-sum supplies preservation of epimorphisms by i_j^*. I read lem-pc-module-pullback-identity-composition and checked it is the tensor pullback comparison needed for i_j^* p_j^* = g_j^*. The chosen twist isomorphism in the hypotheses then gives exactly q_j. Nothing about a projective bundle of finite rank is used.

For Step 4, I checked that lem-pc-module-pullback-adjunction states the natural Hom bijection and left adjunction for this very tensor pullback, not just inverse-image sheaves. Its defining counit formula produces the required factorization. I read the natural open-pullback/restriction isomorphism in lem-weil-pbc-open-immersion-module-pullback-restriction and the composition isomorphism cited again here. The text verifies the counit compatibility on tensor germs a tensor s, both maps evaluating to a s; it does not merely assert that the maps transport. The sectionwise restriction of direct image is verified by equality of the actual section modules and scalar maps. These are elementary consequences of the cited adjunction and explicit definitions, not extra comparison theorems. The three general module identifications are declared as tool uses where appropriate.

Step 5 uses only Steps 3 and 4: a germ lifting through q_j maps under the pulled-back alpha_j to a germ lifting through epsilon. This proves stalkwise surjectivity, equivalently local lifting of sections, and uses no claim that an epimorphism of sheaves is surjective on all sections. Step 6 uses the full quotient-classification statement of the geometry node, which I checked is a bijection on morphisms and quotient isomorphism classes, not only existence of the tautological quotient. Its hypotheses are satisfied by F from Step 2, invertible N from the item, and epsilon from Step 5; its injectivity supplies uniqueness of r.

For the new leaf I read Mathlib/AlgebraicGeometry/Morphisms/Immersion.lean:45, Preimmersion.lean:65, and Separated.lean:61 and :75. The composition instance at :75 specializes in one line: immersion-to-preimmersion, preimmersion-to-Mono, and Mono-to-IsSeparated are all inferred instances, not further mathematical hypotheses. The exact declarations and lines are recorded in mathlib_match. The leanfinder, leansearch, loogle and grep results were read as returned; the supporting search queries and outputs are retained in the command log and node records. The initial broader projective/evaluation searches returned Proj construction, manifold evaluation, and underlying-scheme surjectivity statements, none of which proves this item. A second phrasing was tried for the item and the separatedness search before choosing the match.

I tested the new statement on an identity immersion, the empty scheme, a closed immersion, and an open immersion that is not quasi-compact. All satisfy the stated conclusion; quasi-compactness of the immersion is unnecessary. For the item, E_j=0 forces Z_j empty (there is no rank-one quotient at a nonempty stalk); empty Z gives F=0 and the unique map into P_X(0)=empty. The cover may be infinite and X non-quasi-compact, since separatedness is glued locally while quasi-compactness of g itself is the given hypothesis. The stalk cancellation works for arbitrary modules, including infinitely generated E_j. The classical obstruction to quasi-coherent pushforward without quasi-separatedness is avoided by proving separatedness first.

Against delivery-errors B–E: all new objects and hypotheses are introduced, the single new node is statement-only with empty proof and proof_deps, and its Stacks tag/label and Mathlib lines were read. Existing statements were checked rather than their proofs borrowed. Each non-elementary input has a node citation; every quotation in citations.json was asserted to be a literal substring of the cited statement. The adjunction and surjective-composite arguments are elementary steps, not invented helper nodes. There is no self-citation or use of the item's parent theorem. All steps are under 2000 characters, so no long step hides a further lemma. No SGA source is used.

The first server dry run requested an explicit numeric mathlib_match.line field; I added line 75, already verified from the pinned source, and reran the checks.
