# Q144 stage-1 delivery

Item: lem-cbc-regular-quotient-cone-augmentation.

## Files written

- dag/nodes/sec-smooth-purity/lem-cbc-regular-quotient-cone-augmentation.json: split, nine proof steps; statement and statement dependencies unchanged; inherited metadata and earlier Mathlib searches retained.
- citations.json: one entry per cited node per proof step, with verbatim statement excerpts (full statements when several clauses are used).
- report.md: this report. searches.jsonl records the searches actually executed. write_split.py is a sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched the project source under lean/WeilConjectures for the exact blueprint tag and for scalarCone, tensorScalarCone, quotient/cone augmentation and K-flat change-of-rings concepts. DerivedCategory.reductionIso and reduction_reductionIso_hom in CategoryTheory/DerivedCategory/Monoidal/TensorMappingCone.lean provide the abstract monoidal reduction comparison and its reduction-map identity. They do not directly state the full item: the chain augmentation on arbitrary K-flat module-sheaf complexes, its quasi-isomorphism, and its identification with derived extension into the S-module category. I reused existing DAG statements for the needed ingredients instead of claiming an attachment or adding duplicates.

## WANTED

None. The relevant Stacks sources and both the current blueprint statement/proof and unit are available locally.

## Findings and corrections

The item had an empty proof and no earlier sandbox node or report. Its statement is correct as written. No statement change or STATEMENT-DISPUTED correction is necessary. The only changed mathematical fields are the proof, its dependencies, proof origin, searches and split report. There is no change to a target, chapter, unit route or coefficient category.

Two distinctions matter. A K-flat complex need not have flat terms, so one cannot tensor the given exact sequence termwise and assert exactness. Instead Step 2 tensors its already quasi-isomorphic two-term resolution with the K-flat complex. Also the existing representative-localization equivalence and derived-unit normalization use flat-term K-flat complexes. Step 7 explicitly resolves an arbitrary K-flat P by such an F and cancels the inverted cone map, so no flat-term hypothesis is silently imposed on the item.

The proof is an agent expansion of the principal-resolution and K-flat localization arguments in Stacks, rather than a claim that Stacks states this entire normalized comparison verbatim. The blueprint ancestor is thm-cbc-finite-extension; its sole proof paragraph uses the finite-level constructible landing. This item supplies the quotient comparison used in old steps 2 and 3 of lem-cbc-finite-extension-reduction-cone-bound. I read the main-20261015 blueprint version under sec-six-functors-basics/sk-thm-sf-pf-field and the compact-support unit. Searches of the full imported blueprint for cone augmentation, principal quotient and K-flat, and the DAG searches by tags and concepts, found no blueprint node with this whole statement. same_as remains empty.

## Generic tool uses

The split_report declares the generic tools used from other units: lem-pc-cone-short-exact-quasi-iso (cone projection); lem-weil-pbc-total-tensor-homotopy-cone-signs (signed tensor and K-flat calculus); lem-pur-quasi-iso-cone-acyclic (acyclic-cone criterion); lem-pur-derived-change-of-rings (derived scalar extension); lem-pur-sheaf-ring-derived-coefficient-adjunction (exact restriction and actual unit); lem-weil-pbc-site-derived-tensor-descent (flat-term representative localization); lem-weil-pbc-localization-universal-property (descent and uniqueness); lem-pc-kflat-resolution (flat-term replacement). These supply general homological algebra for the finite-level coefficient reduction; no compact-support assertion is replaced by another route.

## Not duplicates

No new nodes were created. The ordinary-ring principal-cone nodes have different objects; I did not use them as sheaf results. The existing tensor-cone, short-exact-cone, change-of-rings and localization statements are cited directly. No elementary calculation, clause of the item or existing Mathlib fact was made into a node.

## Mathlib searches

The inherited searches were retained. I ran the required msearch.py command for this item with LeanFinder twice using different formulations, Loogle for CochainComplex.mappingCone, QuasiIso, LeanSearch for the K-flat principal-quotient comparison, and grep both for cone augmentation and for K-flat/change-of-rings terminology. All services answered. The exact queries and returned names are in mathlib_searches and searches.jsonl. I read Mathlib/Algebra/Homology/HomotopyCategory/ShortExact.lean, especially descShortComplex at line 53 and quasiIso_descShortComplex at line 137; that result is already the Mathlib leaf lem-pc-cone-short-exact-quasi-iso. I also read RingTheory/Regular/Category.lean: its smulShortComplex is an ordinary-module statement and does not give the ringed-site derived comparison. The remaining hits supply localization infrastructure, tensor construction or unrelated flatness facts, not a one-line specialization of the whole item.

## Review by Q144

I read coord/delivery-errors.md B through E in both copies, the worker brief, stage-1 contract, GOAL, SETUP's three-level rule, and the chapter/unit records. For the item I read sites-cohomology.tex at Tags 06YM (lemma-derived-tor-exact), 06YN (definition-K-flat), 06YP (lemma-K-flat-quasi-isomorphism), 06YS (lemma-K-flat-resolution), 06YT (lemma-derived-tor-quasi-isomorphism-other-side), the construction preceding 06YU (definition-derived-tor), 0G7D (lemma-factor-through-K-flat), 06YY (lemma-derived-base-change), and 07A6 (lemma-adjoint). I checked the tag-to-label mapping, the tensor remark in derived.tex and its derived-adjunction statements. I read the project DerivedChangeOfRings.lean for the actual universal comparison and the scalar-cone source for its coordinate conventions. No prohibited SGA source is used. There are no new-node sources to audit.

For Step 1, I opened lem-pc-cone-short-exact-quasi-iso: its statement gives exactly the cone-to-third-object map, including the zero shifted component. The assumed sheaf exactness is precisely its hypothesis after placing the three objects in degree zero. No sectionwise surjectivity or point detection is assumed.

For Step 2, I opened lem-weil-pbc-total-tensor-homotopy-cone-signs: it states the right-tensor cone comparison, the signed symmetry, and preservation of arbitrary-endpoint quasi-isomorphisms by a K-flat fixed factor. I use its right tensor with P, with B in the first variable; its cone comparison is identity on both summands. With B in degrees -1 and 0, the differential is exactly (dy+rx,-dx). Swapping the degree-zero S factor has sign 1. These facts give the actual map y tensor 1, rather than an unspecified isomorphism to some cone. The balanced tensor-unit formulas are written in the step.

Step 3 is an elementary balanced-tensor calculation: phi(r)=0 is exactly what makes a a chain map, R-linearity of h makes the diagonal map a chain map, and evaluation on the two summands proves both identities. It invokes no hidden non-elementary theorem.

For Step 4, the same tensor statement gives the left cone comparison and homotopy compatibility. I opened lem-pur-quasi-iso-cone-acyclic and def-pc-kflat-complex: for an acyclic E, r on E is a quasi-isomorphism by the cohomology definition, so its cone is acyclic. This proves B is K-flat and hence C_r preserves all quasi-isomorphisms by the cited tensor statement. This uses neither regularity of r on P nor boundedness. The shifted sign is explicitly recorded.

For Step 5, I read clause (1) of lem-pur-derived-change-of-rings and the exact-restriction clause of lem-pur-sheaf-ring-derived-coefficient-adjunction. They give exactly quasi-isomorphism preservation for K-flat endpoints and preservation by scalar restriction. The same small site and commutative ring sheaves satisfy their hypotheses. The elementary termwise homotopy equation is included.

For Step 6, I opened lem-weil-pbc-site-derived-tensor-descent and used its actual equivalence from localization of the flat-term K-flat homotopy subcategory, not merely existence of resolutions. I also opened lem-weil-pbc-localization-universal-property, whose statement includes descent of natural transformations, preservation of their invertibility, and uniqueness. The site's smallness in the module universe is in the item, and matches the equivalence's hypothesis. Change-of-rings supplies the canonical computation identification of the second functor. This establishes naturality for every derived morphism without assuming every such morphism is an actual chain map.

For Step 7, lem-pc-kflat-resolution really states both K-flatness and flat terms of F. Change-of-rings really computes on every K-flat complex. I wrote the complete comparison square and cancellation; thus the normalization at non-flat-term K-flat P is not inferred from a flat-term-only statement.

For Step 8, I read the derived scalar adjunction's unit clause (1): it identifies the actual adjunction unit with x tensor 1, but only initially on flat-term K-flat representatives. That is exactly the class used here. The earlier equivalence and the uniqueness of natural-transformation localization extend the identity to all objects. For Step 9 the canonical comparison is written as (Qt)^(-1)Qs; its cocycle is an explicit cancellation. Naturality was already obtained for all derived morphisms in Step 6, so no unproved choice of a comparison chain map is used.

I checked small cases on the one-point site: R=Z, r=2, S=F_2 and P=Z[0] gives the familiar resolution in degrees -1 and 0 and the quotient in degree zero; shifting P changes the total-tensor sign exactly as in Step 4. For P=0 all maps are the unique maps of zero complexes. If r is a unit then S=0 and the cone is acyclic, consistently with the claimed quasi-isomorphism. If r=0, injectivity forces the zero ring sheaf, so the hypotheses exclude any nonzero-ring counterexample. These checks also expose why the non-flat module Z/2 in degree zero cannot simply be substituted for a K-flat P. No point or enough-points hypothesis was introduced.

Every proof citation has a verbatim entry in citations.json. Every step is shorter than 2000 characters. I checked all B requirements on form, self-contained statements and honest searches; C requirements on statements actually supplied, complete citations and no cycles; D requirements on carrying the argument without moving a clause to another node; and E requirements on exactness, coefficient categories, signs, normalization and explicit comparison maps. The only new file under dag/nodes is the item itself.

## Unfinished work

No mathematical work remains for this stage-1 split. Server review_split passed. The full deliver.py --no-push exited successfully with OK at 17fe17b01a7, including the server DAG and delivery-preflight checks. A final dry run of this report and direct push follow under the authorized delivery workflow.
