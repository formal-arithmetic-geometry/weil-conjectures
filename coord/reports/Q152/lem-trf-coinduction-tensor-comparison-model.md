## Worker report

Written: dag/nodes/sec-trace-formula/lem-trf-coinduction-tensor-comparison-model.json, statement, split; Mathlib verdict no match. Also citations.json. No Lean written or compiler invoked; all writes remain in the assigned sandbox.

## New nodes

None. The existing coinduction adjunction and K-flat tensor functor suffice. The balanced formula, differential verification, evaluation-at-one composite and adjunction equations are explicit proof steps, not new lemmas.

## Attachments

None. Searched lean/WeilConjectures for the item id and blueprint tag, coinduction/coextendScalars, and tensor/coinduction combinations. The hits concern discrete modules, scalar extension and sheaf coinduction; none states this ordinary unbounded derived comparison. No claim of completion rests on a sorry declaration.

## Literature

No WANTED sources. Read Stacks dualizing.tex, Tag 0A70 (lemma-right-adjoint) and Tag 0A71 (lemma-RHom-ext), including their proofs; more-algebra.tex, Tag 06XZ (definition-K-flat), lemma-K-flat-quasi-isomorphism, lemma-derived-tor-quasi-isomorphism-other-side, the intervening derived-tensor construction and Tag 06Y6 (lemma-derived-base-change); sites-cohomology.tex, Sections 0A8X (section-hom-complexes) and 08J7 (section-internal-hom). The detailed tensor-counit calculation is supplied by this worker, so proof_origin.by is agent. No SGA source is used.

Read the current blueprint at literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md and its .proof.md, together with the chapter and unit records. This item is a technical algebraic dependency through the recorded via chain, not the unit statement or its geometric proof. No chapter/unit realization fields are changed.

## Existing-node and Mathlib searches

Searched the whole DAG for Tags 0A70 and 0A71 and coinduction/tensor terms. Read the statements of lem-trf-coinduction-total-hom-model, lem-trf-derived-bimodule-tensor-hom, lem-trf-perfect-algebra-coinduction-tensor, lem-trf-perfect-algebra-dual-evaluation and lem-trf-coinduction-shift-scalar-model. The total-Hom adjunction is different; the perfect-algebra comparison adds perfectness and invertibility and depends on the present item, so it cannot be cited to prove this item. No new node was created. Whole-blueprint searches using blueprint_refs.py for coinduction tensor, 0A70, and tensor.*Hom returned no matches; same_as remains empty. The ancestor command confirms lem-trf-local-term-locality, and the existing precise from.place and via chain are retained.

Ran all new Mathlib queries through the required msearch.py command; searches.jsonl records the exact tool/query pairs and returned hits. Two semantic phrasings, Loogle, LeanSearch and two grep queries were read. Read Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:441-540 and 590-675: coextendScalars at 520 and restrictCoextendScalarsAdj at 659 are module functors, not unbounded derived comparisons. Read Mathlib/LinearAlgebra/Contraction.lean:40-80: dualTensorHom at 54 and dualTensorHom_apply at 69 concern ordinary module duals with target R, not Hom(B,J) for arbitrary K-injective J. The semantic hits about injective resolutions, Tor, representations and module closed adjunctions do not state all clauses. All services answered; no unavailable response was relabelled as no match. Prior recorded searches are preserved, and this run's exact logged records are appended.

## Errors and unfinished work

The imported statement needs no correction. It asserted no invertibility, and no perfectness, flatness, Noetherianity or boundedness was inserted. The original node had no proof; its main missing details were the identification of I using a=q(1 tensor j), the tensor sign, and the counit computation with the inverse of 1 tensor j. These details are now written out. No work on the assigned split is left unfinished. The cited generic tensor node belongs to another unit and is declared as a tool in split_report.tool_uses; its clauses (2)-(3) are exactly the computation needed, without changing the trace-formula route.

## Review by Q152

I read the item and its sources against the unbounded statement. Tag 0A70 gives the right adjunction for an arbitrary ring map; Tag 0A71 explicitly computes coinduction on K-injectives as Hom(B,I). Neither assumes flatness or a Noetherian ring. I retained the full statement and all original metadata. There are no new-node statements to check or search. I checked delivery-errors B through E as follows.

Step 1 uses def-pc-module-kflat-complex for preservation of quasi-isomorphisms: this statement explicitly includes the equivalent criterion, so it is not an appeal to a bare flatness definition. It applies to j:R[0] to J because F is K-flat. The quasi-isomorphism q is one of the chosen resolutions, hence a=q(1 tensor j) is also a quasi-isomorphism. def-pur-derived-internal-hom explicitly says that every complex has a K-injective resolution and permits other K-injective representatives, on the one-point site as here. lem-trf-derived-coinduction-adjunction explicitly provides the B-action, the K-injective model, the evaluation counit, and choice independence. Clause (2) of lem-pc-derived-tensor-second-factor-functor computes tensor using a K-flat first factor for an arbitrary B-complex second factor. Thus I did not assume V, J or B is flat. These are the non-elementary inputs of this step.

Step 2 cites the displayed action in that coinduction statement, the actual differential formula in def-pur-hom-complex, and the direct-sum terms and tensor differential in def-pc-tensor-complex-sheaves. I checked R-balancing, R-linearity in b and B-linearity at bc in the written formulas. Since B[0] is concentrated in degree zero, the Hom differential has no source term. The two remaining differential summands match term for term with sign (-1)^p. Finite support in the direct-sum totalization suffices even when F and J are unbounded. This is a routine computation from the cited definitions, correctly marked elementary; no Hom/tensor isomorphism or finite-projectivity assertion is hidden in it.

Step 3 uses the same coinduction theorem for both counits and its adjunction, and tensor-functor clause (3) for the representative of tensoring the counit. I checked the domains: e_J maps UV to J and represents the counit only after the target is identified through j. Likewise I is identified with K through a, not through q alone. The equation [q]=[a][1 tensor j]^{-1} is therefore essential. Evaluation at 1 now gives exactly m_K, so injectivity of the adjunction bijection proves that the localized t is sigma_K. This step supplies the comparison rather than citing a new restatement of it.

Step 4 uses the explicit underlying-R identification in lem-trf-derived-coinduction-adjunction and the K-injective formula in def-pur-derived-internal-hom. The scalar comparison is the actual same formula q(f tensor h(b)); the text writes its entire evaluation procedure and relies on the differential calculation of step 2. No assertion about scalar restriction preserving an unspecified internal Hom, or about sigma being invertible, is used.

Step 5 uses the canonical representative comparisons and functors stated in the tensor and coinduction nodes. Uniqueness of an adjunct proves choice independence after those particular identifications. I wrote both counit composites for naturality and checked they equal u m_K=m_K' U(u tensor 1). This proves naturality for an arbitrary derived morphism, so no unsupported lifting of u to a chain map is needed. The final cancellation is injectivity of an adjunction bijection, an elementary categorical inference.

For B=R with J=R[0], the map is the tensor-unit identification followed by q, and the stated normalization is the identity after localization. For K=0 all maps are zero; acyclic K-flat representatives remain covered by the same quasi-isomorphism argument. For a nonflat quotient such as Z to Z/2, the argument still only needs K-flatness of F; it neither replaces RHom by underived Hom nor claims sigma is invertible. For the zero ring B the two B-complexes are zero. In arbitrary unbounded degrees, B[0] contributes only degree zero to Hom while the tensor inputs have finite support, so no convergence/boundedness hypothesis is missing. These checks found no false edge case and required no statement correction.

Every proof citation has a verbatim public-statement quote in citations.json, read against the specific claims above, and proof_deps is precisely the union of uses. Each of the five steps is under 2000 characters; there is no long step concealing a standard comparison. The unit route, source fields, pointers and all maintainer fields are unchanged. No new ids means no duplicate pairs to resolve. The checks do not depend on another node's proof or on one of this item's own clauses renamed as a lemma.
