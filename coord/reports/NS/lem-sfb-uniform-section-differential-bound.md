# Stage-1 delivery: lem-sfb-uniform-section-differential-bound

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-uniform-section-differential-bound.json: statement, split; original statement preserved, ten proof steps, no new nodes, no new Mathlib leaves.
- citations.json: one verbatim statement quotation for every step/node citation.
- searches.jsonl: actual msearch.py results, including exploration of a possible denominator-clearing helper which was not created because existing nodes suffice.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id, section differential defects, torsion/differential bounds, and Neron/defect terminology. The hits about chain-complex differential defects and unrelated affine-section annihilators do not state this result. There is no exact project declaration to attach. No Lean was written, compiled or built.

## Literature wanted

WANTED: Bosch–Lütkebohmert–Raynaud, Néron Models, §3.3 Proposition 3 and its proof, printed pp.66–67, for lem-sfb-uniform-section-differential-bound. The local literature/bosch-lutkebohmert-raynaud-neron-models.pdf named by the inherited source is absent. I read the primary scan at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf, PDF pages 72–73, together with the preceding definition and Lemmas 1–2. This delivery does not write literature/ or the wanted list. The proof is marked agent, as required when the named local source is missing.

## Findings and proof choice

The imported statement is sound; no STATEMENT-DISPUTED or statement correction is needed. BLR bounds Jacobian minors separately on the schematic closures of the different-dimensional generic pieces. The delivery instead supplies a module proof of the same boundedness input: finite presentation lets a generic projective splitting be multiplied by a fixed power of pi to descend integrally. That power kills torsion after every evaluation into A. Smith form bounds the number of torsion generators by the number of differential generators, and a fixed cyclic quotient of A has finite length. The maximum over the finite affine cover finishes.

This is explicitly an agent proof, not a claim that BLR writes the projective-splitting argument. The current unit record is sk-thm-sf-ctf-stability, inherited from the created.item chain; this auxiliary local-algebra input is not a key node realizing that unit. No unit or chapter is changed. tools/blueprint_refs.py ancestor returns None; I preserved the existing null ancestor and its via chain. Searches of the whole imported blueprint for differential, projective, torsion length, 0583, projective localization, localized module, Smith and factor through found no duplicate of the item or of the prospective helper. No new helper was needed. The algebraic modules and Hom comparisons already have nodes.

## Not duplicates

There are no new nodes. In particular, a putative node asserting a pi-power factorization through a finite free module was not created: it would package the short calculation in Steps 5–6 from the existing flat Hom base-change theorem, localization and the definition of projective. The existing defect criterion treats one section and explicitly has no uniform bound; the existing Smith and finite-length nodes are used for precisely their algebraic conclusions.

## Review by NS

I read the worker brief, stage-1 contract, chapter/unit records, GOAL.md, the three-level and tool-use rules in SETUP.md, and delivery-errors.md B–E (including both copies). I checked each of the ten steps against the actual statements of its cited nodes and wrote citations.json from those statements. No non-elementary step exceeds 2000 characters. Every proof dependency is the union of the step citations.

1. The chosen A is an algebraic strict henselization, whereas lem-sc-strict-henselization-dvr states the geometric strict-local-ring form. I supplied lem-exc-affine-strict-local-ring-comparison, whose statement actually identifies them over R, and then used the former node's explicit injectivity and DVR conclusions. The PID node supplies Noetherianity of R. I read Stacks 0AP3 (more-algebra.tex, lemma-henselization-dvr), 04HX and the DVR characterization 00PD. This avoids the C4 error in the earlier defect-criterion review. We only need the nonzero image t of pi; no unproved preservation of a chosen uniformizer is used.

2. def-weil-finite-type-morphism explicitly includes a finite affine cover over the affine base. The local-spectrum argument is written out: an open containing the closed point contains all its generalizations. No separatedness or affine-intersection theorem is used. This is BLR's finite affine reduction.

3. lem-trf-relative-differential-sheaf-base-change explicitly includes quasi-coherence, the affine identification and finite type of differentials. lem-weil-pbc-finite-type-algebra-noetherian gives the Noetherian ring B, and lem-sc-noetherian-finite-module-finite-presentation then applies to the finite module M. I read 01UT/01V2, 00FN (Hilbert basis permanence) and the finite-module/presentation statements. This supplies the finite-presentation hypothesis required later by the Hom comparison; finite generation alone over an arbitrary B would not suffice.

4. The same differential node supplies the actual generic base-change identification, and lem-weil-pbc-localization-tensor gives its localization realization. lem-ag-smooth-relative-differentials-finite-locally-free says exactly finite locally free with variable rank. Principal refinement uses the definition of the Zariski topology; lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact supplies finite extraction and the unit-ideal conclusion. On each chosen principal open, lem-weil-pbc-module-pullback-affine-sections plus the localization tensor theorem supplies the localized module, so lem-sc-affine-standard-cover-finite-projective applies with the finite-free modules it requires. I read 02G1, 00NX (especially (7) implies (3)), 00E0/00E8, 01I9 and 00DE/00DK. No constant rank, equidimensionality or freeness of the entire generic module is presumed.

5. The localized surjection and its right inverse are justified by an explicit fraction lift and the lifting characterization in def-weil-pbc-projective-module. This definition really does include the lifting property, unlike a citation of a definition that only names projectivity. lem-weil-pbc-localization-flat gives the flat B->C map required by lem-weil-pbc-flat-base-change-hom-finitely-presented; its source M is finitely presented by Step 3. That latter node explicitly states the canonical tensor-Hom bijection and its formula. Together with lem-weil-pbc-localization-tensor it gives the displayed Hom localization, with no finiteness assumption on the Hom module. I read Stacks 087R part (1), 00HT and 0583 (lemma-hom-from-finitely-presented), and checked the nearby Mathlib exists_lift_of_isLocalizedModule at FinitePresentation.lean:366. The candidates found by msearch.py did not make the whole item a Mathlib leaf. Combining finitely many denominators is explicit.

6. def-weil-pbc-module-localization-away explicitly states that an element becoming zero is killed by a power. Applying that equality separately to the finitely many images of generators and then taking a maximum proves the exact integral identity qu=pi^N id, not just its localization. This corrects the potential gap hidden by the phrase “clear denominators”; no extra unproved descent lemma is used.

7. The affine pullback node identifies the original section module with M tensor_B A; def-weil-module-base-change explicitly states compatibility with composition and identities. The tensor identity is also checked on generators. Any torsion vector maps to zero in A^m because the same nonzero scalar kills its image and A is a domain. Thus t^N kills the torsion, and q_A is surjective because its specified images generate. I did not assume pullback preserves a kernel or an exact sequence.

8. lem-sfb-pid-submodule-smith-bases allows unequal ranks and arbitrary submodules N subset O. I used J subset A^m with O=A^m, not the full-rank-only variant. I read its exact Mathlib theorem Submodule.exists_smith_normal_form_of_le at LinearAlgebra/FreeModule/PID.lean:492–497. The quotient coordinates are written explicitly, and they show that the torsion has at most m generators. The c_i are nonzero since they multiply genuine basis vectors to basis vectors of J. Their being units is allowed.

9. lem-sc-dvr-dimension-one and the PID Noetherian node verify the hypotheses of lem-weil-pbc-dim-le-one-principal-quotient-finite-length; t^N is a nonzerodivisor, including N=0. I read the first assertion of Stacks 00PE (lemma-finite-length) and 00IV (lemma-length-additive). The surjection from at most m copies of A/(t^N) is explicit, rather than an unsupported assertion that a submodule has at most as many generators. The length bound follows from the cited additivity applied to the direct sums and the kernel short exact sequence. The integer L_U is independent of the section; thus so is c_U=m L_U.

10. Every section lands in a chart by Step 2. Taking the maximum of the finitely many fixed chart constants gives the required integer. No maximum over an infinite set of sections or compactness of that set is used.

Small cases checked: empty X or empty set of sections (c=0 suffices); M=0 and m=0; a smooth affine-space model (one may take N=0, torsion zero); the flat nodal model xy=pi^2 with section (pi,pi), where the evaluated differentials are A^2/A(pi,pi), with one cyclic torsion summand; generic components of different smooth dimensions, for which Step 4 uses finite projectivity with variable rank rather than globally free differentials; and a chart with empty generic fibre, where localization is zero and the same finite-generator power argument works. None requires completion, excellence or properness.

All off-unit theorem uses are generic algebra or differential tools and are declared in split_report.tool_uses where needed; none supplies a replacement constructibility or trace argument. There are no new nodes and hence no new-source tag duplicate pairs to distinguish. The unchanged item source and its previously recorded searches remain present, with actual fresh item searches appended. All exploratory searches are in searches.jsonl and their hits were read; no unperformed search was recorded.

## Unfinished work

No mathematical part of this one-level split remains. The required server dry run exited successfully: preflight passed at 2abceb4ba6e, including tools/check_dag.py and tools/review_split.py. The item statement was also compared verbatim with the current read clone and is unchanged. This report update is included in a final dry run before pushing.
