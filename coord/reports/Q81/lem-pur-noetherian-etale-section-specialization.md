# Stage-1 report: lem-pur-noetherian-etale-section-specialization

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-noetherian-etale-section-specialization.json: existing statement node, split into twelve proof steps; Mathlib verdict: no match.
- citations.json: 52 verbatim statement extracts, one for every step/node citation.
- searches.jsonl: the search command's actual results for Q81, retained unmodified.
- report.md: this report. No new nodes and no Mathlib leaves were created. prepare.py is sandbox-only preparation code, not a delivery file.

## Attachments

None. I searched the read-only slopmaster2 WeilConjectures source for the blueprint id, NoetherianSectionSpecialization, existsUnique_normalized, sectionInvariant, normalCone, and deformation. No project declaration states this ordinary-etale Noetherian theorem. The existing node also records no slopmaster2 declaration. The maintainer-owned Sheaf/Paper declaration metadata and earlier review records were retained, not treated as an attachment or as a finished proof.

## Literature wanted

None. The current blueprint statement and proof are available at literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/{_section.md,sk-thm-dnc.proof.md}; the Stacks sources used for the chart and flatness checks are present. This remains an agent-written ordinary-etale adaptation of that blueprint argument, and proof_origin says so.

## Corrections and retained work

The Q81 sandbox initially held only dispatcher marker files: no split, report, search log, citations or delivery result was available to resume. I copied the current repository item, which already contained an eleven-step Q71 proof and prior maintainer/stage-2 review metadata but had status unsplit. I retained its statement, full mathematical argument, original searches, source citations, creation provenance and maintainer-owned fields. I made no change to any Lean or unit file.

The item statement is unchanged. I added the existing relative-dimension permanence citation to the first step, separated the compactifiability hypotheses from the actual local dualizing comparison (old step 7 becomes steps 7 and 8), and updated later step references. I removed cor-amb-affine-space-adjunction from stmt_deps because it is a proof tool, not a notion in the statement. I removed def-pur-normal-bundle because its fixed field/pro-etale setting does not define the normal bundle over the general Noetherian base here: this item already defines N explicitly using E and cites def-asd-vector-bundle-zero-section. I retained the general conormal-algebra and ideal-sheaf conventions. No coefficient category was silently identified with another one.

The previous same_as list named sk-thm-dnc and prop-pur-dnc-family-constancy. After reading their statements, I set same_as=[]: both are field-based pro-etale assertions, whereas this item is an ordinary unbounded-etale assertion over arbitrary Noetherian schemes. thm-pur-dnc-invariance has the same restriction. Their proofs explain the route, but their statements cannot be invoked as this theorem. The blueprint ancestor command returns null for this creation chain, and I preserved it and its meaningful from.place. The item is a supporting node, not the unit key node, so no realized fields are changed. All inherited tool-use declarations are retained in split_report; the maintainer-owned tool_uses is unchanged.

## Searches and reuse

I searched the whole blueprint for deformation and normal bundle, and the DAG for normalized comparison/family comparison/specialization. Existing blueprint alternatives have the coefficient/base restrictions explained above. I read all 36 proof dependency statements, as well as the additional statement dependencies concerning conormal algebras, normal bundles, module pullback and ideals. No new lemma was needed: flat tensor exactness, smooth/etale permanence, locality, compactification, affine adjunction, sheaf gluing and mate pasting already have nodes. The polynomial Rees computation is written out rather than relabelled as a new node.

For the item, I ran msearch.py with LeanFinder, Loogle, source grep, and LeanSearch, then a second semantic phrasing. I read every returned hit. They concern scheme normalization, standard-etale and smooth algebras, affine coordinates, and differentiable manifold sections, not exceptional-dualizing deformation comparisons. Both the dualizing-name Loogle query and the deformation/sectionInvariant/normalCone Mathlib/AlgebraicGeometry grep had zero hits. The exact command results are in searches.jsonl and appended to mathlib_searches; inherited searches are retained. No unavailable service is recorded as absence and no unrun search is asserted.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. The item vs sk-thm-dnc / prop-pur-dnc-family-constancy / thm-pur-dnc-invariance distinction is the ordinary-etale category and general Noetherian base, as described above.

## Review by Q81

I read the current main-20261015 sk-thm-dnc statement and its full Local construction/Gluing proof, the chapter and sk-thm-purity-transport unit record, and delivery-errors B--E. The proof retains the chart, normalization, connected-fibre and mate-comparison route, not any SGA trace route. No SGA source is used. There are no new nodes whose statements or sources require an additional review. Below I describe what each proof step takes from the actual cited statements; citations.json contains their verbatim extracts.

1. The smooth normal-form statement really gives an etale map after shrinking both schemes; smooth-relative-dimension permanence together with the given fibre dimensions fixes the number of variables to d. The definition of an etale morphism gives flatness. Affine-source separatedness, etale and separated base-change, and the clopen-section statement apply to P_i=e_i^{-1}(0). Removing the other clopen component makes the centre square Cartesian. The affine flatness criterion then really supplies flatness of B over P=R[x], not an unwarranted polynomial identification of U_i.

2. Flat tensor exactness applies because B is flat over P, as established in step 1. I checked the degree pieces J^m and the injection into the Laurent polynomial ring, and the monomial bijection x^alpha t^k <-> u^alpha t^(k+|alpha|). Thus the tensor product identifies the actual Rees subalgebra, including its multiplication. The homogeneous calculation also identifies gr_I(B) with Sym(I/I^2), canonically on generators, and shows E is free of rank d on these centre charts. Canonical maps glue without choosing an identification on overlaps. This is a written algebra calculation from the cited exactness statement, not a quotation of an uncited blowup theorem.

3. Etale base change gives the deformation chart over A^d_(A^1_Si). The affine-space smoothness and smooth-permanence statements supply its relative dimension, and the punctured part is the base change of g. I checked the cover: t=0 lies over the centre because I=t(I/t), while t invertible is V times G_m. Quotient by t gives the graded pieces I^m/I^(m+1), evaluation at 1 gives V, and both augmentations give the stated sections. Finite generation of I makes the Rees algebra finite type; the cited finite-type-Noetherian theorem applies to D->V. The separatedness argument writes both diagonal closed immersions explicitly using multiplication and the diagonal of g, rather than assuming separatedness of an arbitrary chart.

4. The new chart B'=B tensor_R R' remains etale and hence flat over R'[x], so the same monomial/exactness argument works even if R' is not R-flat. The canonical maps preserve b, t, x_j/t and the degree-one classes, so they preserve the section and both fibre identifications. The regular sequence survives because the variables form a regular sequence over every coefficient ring, and the successive injections are preserved by the flat P'-module B'. Thus the later base-change comparison really refers to the base-changed deformation, including for nonflat morphisms.

5. I checked the exact coefficient hypotheses of thm-asd-smooth-tensor: A is finite, N=ell^n kills A and is invertible; all three maps are smooth, separated and compactifiable, and all sources/bases are Noetherian. In particular the result states the rank-one sheaf conclusion on the ordinary entire unbounded category, without an orientation choice. The inverse-image module theorem supplies exact termwise pullback. The finite-type-Noetherian statement covers affine space and the vector bundle. No field-only smooth-purity theorem is substituted.

6. prop-asd-smooth-base-change states the isomorphism for the canonical beta obtained from the compact-support counit, and I apply exactly that map to the two closed fibres and then to their sections. The maps g and pi and their compactifiability are the hypotheses supplied here. Exact inverse image commutes with the common shift. Thus theta and eta are specified canonical fibre maps, not arbitrary orientations.

7. I checked all compactifiability hypotheses before the next step invokes etale locality: etale affine charts are locally of finite presentation and quasi-compact, hence finite type; the open sources are Noetherian and their opens are quasi-compact by the cited open-subscheme statement. All maps are separated; their Noetherian targets are quasi-compact and quasi-separated, so the final clause of thm-nagata-compactification applies. This is a finite verification of the hypotheses, not a new general compactification lemma.

8. lem-amb-etale-adjoint-locality explicitly identifies u^* f^times K with (fu)^times K for separated finite-type etale u when both maps are compactifiable. Step 7 verifies those assumptions, for both the open inclusions and the chart maps. cor-amb-affine-space-adjunction is on the entire ordinary etale category, and the unique-right-adjoint theorem identifies its right adjoint with the chosen omega. lem-asd-etale-finite-twist-pullback states the Tate pullback isomorphisms; prop-asd-smooth-base-change identifies the base-localized objects. I checked h_i's type as an automorphism of C|Si and that multiplication by its pulled-back inverse changes the restriction at 1 to exactly theta_i. This is the main local construction of the item, not a separate lemma that restates the conclusion. Separating step 7 leaves every non-elementary step below 2000 characters.

9. The degree-zero derived functor is fully faithful by the cited statement; it gives actual sheaf maps after the common shift. The scalar of an endomorphism of a rank-one module is basis-independent since A is commutative (the text writes vuv^-1=u), so the ratio is a section of the constant unit sheaf on each geometric affine line. The polynomial-domain, closure-of-prime, irreducible-connected statements give connectedness of that line. The set-valued constant-section lemma applies with E=A^times and algebraically closed Omega; normalization fixes its value at 1. Exactness of geometric stalks passes to the image of a difference, and conservativity makes that image zero. Thus equality is proved on all stalks, not inferred from a single section point alone. The same ratio argument proves global uniqueness.

10. The sheaf-Hom gluing statement really applies to maps agreeing on this cover and its pairwise overlaps. Their inverses also glue, and full faithfulness returns the derived isomorphism. The fibre formula is delta=eta (i0^*kappa)^-1; this matches the statement after its stipulated canonical fibre identifications. I checked the direction of the inverse.

11. The unbounded compact-support-comparison node states compatibility with composite changes of base, and the mate-pasting statement gives the composite equation for b_h,vw. The smooth-base-change statement identifies these b maps with the canonical exceptional maps used in step 6. I checked both decompositions of bar(v) i'_r=i_r v: they give theta' i1'^*b_F=b_C v^*theta and eta' i0'^*b_F=b_N v^*eta. This is the missing content that exactness alone would not provide.

12. Smooth base change makes b_C,b_F,b_N invertible. I checked the source and target of kappa^v=a'^*b_C (bar(v)^*kappa) b_F^-1, its normalized restriction using step 11, and application of uniqueness from step 9 over S'. The step-4 geometry verifies the same assumptions there. Substituting the eta equation in the inverse zero-fibre formula gives delta' b_C=b_N v^*delta. The conclusion is therefore about the fixed canonical maps, not an unspecified isomorphism.

Small-case checks: the empty base has only the unique morphisms involved; d=0 makes the centre charts B=R and gives R[t], while the complement of the section lies in the punctured deformation; the monomial formula has no variables and remains valid. For a genuinely etale non-polynomial chart, B=k[x,y]/(y^2-1-x) localized where 2y is invertible, the centre component y=-1 is removed before I=(x) and B/I=k are used. This confirms why U cannot be silently identified with affine space. For a nonflat change R=k[epsilon]/(epsilon^2)->k, the identity polynomial chart gives R[t,u] tensor_R k=k[t,u]; the proof for arbitrary etale B uses flatness over R'[x], not flatness of this change. No added hypothesis on S' is needed.

## Unfinished work

No part of this stage-1 split remains unresolved. Its cited unsplit nodes remain separate DAG tasks. Delivery is conditional on the required server-side dry run and push completing successfully; their final result is reported by the delivery command.
