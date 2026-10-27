# Stage-1 delivery: lem-per-noetherian-formal-affine-coherent-modules

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-formal-affine-coherent-modules.json — statement split into eleven steps; not a Mathlib leaf.
- citations.json — 34 verbatim statement quotations, one for each step/node pair.
- report.md — this report.
- searches.jsonl — actual msearch.py results; the original item's recorded searches were retained and five searches run here were appended to its node.
- write_split.py — sandbox-only reproducible JSON assembly; not part of the node delivery.

New nodes: 0. New Mathlib leaves: 0. No unit record was changed.

## Attachments

None for the item. The exact blueprint tag, Spf/FormalScheme, and formal/coherent concept searches in lean/WeilConjectures returned no declaration for module sheaves on the formal ringed space. Existing AlgebraicGeometry.coherentFormalModules_affine in lean/WeilConjectures/AlgebraicGeometry/CoherentFormalModulesAffine.lean:56 instead concerns quotient systems of coherent sheaves on the ordinary affine scheme. Its statement and proof were read, and its existing node is cited in steps 9 and 10. It cannot attach this item's exactness, formal ringed-space realization, tensor, and restrictions.

## WANTED

WANTED: EGA I, 10.10.2 and 10.10.5 (also 10.11.3–4), original finite-module/coherent-module correspondence and quotient-system characterization, for lem-per-noetherian-formal-affine-coherent-modules. EGA I is not in literature/ega. I read the available EGA III.1 PDF, Proposition 4.8.8 (printed p. 148) and Scholie 5.1.7 (printed p. 150): these explicitly recall the relevant Hom correspondence and quotient-system description. I did not download or pretend to read the absent EGA I proof. The supplied proof_origin is by agent, assembling the available Stacks statements with the local presentation argument.

## Audit of imported material and corrections

The imported item was unsplit and had no Lean declaration attached. Its mathematical statement is retained verbatim. Its statement dependencies now additionally include the existing definition of sectionwise sheaf inverse limits, which its explicit inverse-limit construction uses.

The main missing argument was the distinction between coherent sheaves on the formal ringed space and coherent quotient systems on Spec R. The existing 087W node proves the latter, so it cannot alone prove the item. Steps 4–8 establish the quotient and reconstruction comparisons before steps 9–10 use 087W. No node was introduced that merely restates an item clause.

The item's source mentions EGA I as unavailable. This is retained and explained; the proof is explicitly agent-written. The current latest blueprint ancestor has Step 3 on duality/cosupport, not an explicit formal-geometry paragraph. The pre-existing created.item ancestry reaches this algebraic tool through the regular-local-model/purity refinement. The blueprint.from.place now says so, rather than suggesting that formal charts are literally in the current ancestor's proof. I read the latest ancestor .md/.proof.md, latest unit _section.md, and both DAG chapter/unit records. No chapter or unit route is replaced.

I corrected my draft source tag for right exactness of tensor from 00DD to 00DF after checking tags/tags and algebra.tex. I also made explicit the ordinary-R-module interpretation of the quotient sheaves after closed pushforward, using the section formula; this prevents silently identifying sheaves on different spaces.

## Not duplicates

No new nodes were created, so there are no new/existing pairs.

DAG searches covered formal spectrum, formal affine, completed localization, coherent ringed-space modules, finite presentations, exact completion, finite submodules, and relevant Stacks tags, by whole-DAG statement and source scans. Blueprint searches were run with tools/blueprint_refs.py search for "formal affine", "coherent formal", "completed localization", "coherent structure", and "01BY"; all had zero imported blueprint matches. The ancestor command gives lem-per-artin-gabber-affine-curve, matching the existing field. The useful facts found in the whole DAG were reused, especially lem-weil-pbc-coherent-formal-modules-affine, lem-per-formal-affine-principal-refinement, lem-weil-pbc-completion-exact-finite-modules, and lem-weil-pbc-coherent-modules-kernel-cokernel-sum.

## Mathlib searches

The five NV searches in searches.jsonl are real msearch.py calls. I read every returned hit. The two LeanFinder phrasings concern the formal-affine equivalence and reconstruction from infinitesimal quotients. Returned algebraic-completion results (AdicCompletion.map_exact, ofTensorProductEquivOfFiniteNoetherian, flat_of_isNoetherian) supply generic algebra only and are already represented by existing nodes. Returned forgetful functors fullyFaithfulForget and Scheme.Modules.fullyFaithfulToPresheafOfModules do not assert full faithfulness of completed sheafification. The LeanSearch results Scheme.ΓSpecIso and AffineScheme.ΓIsEquiv concern ordinary affine schemes. Loogle with "FormalScheme", "Coherent" and the required grep found no hits. These services ran successfully; none is recorded as unavailable. The earlier Q106 item's searches remain unchanged.

## Review by NV

I read delivery-errors B–E whole, then checked this proof with each cited node statement open. The citations file copies complete statements so that the exact hypotheses and the clause used remain visible. This report explains their actual uses rather than treating the successful quotation check as mathematical evidence.

1. I read formal-spaces.tex section-formal-schemes-EGA, Tag 0AHY, including its formula for sections on D(f). def-pur-sheaf-inverse-limit explicitly computes limits sectionwise, also for rings. lem-weil-pbc-spec-module-tilde-sections explicitly gives localization sections and canonical restrictions. These justify the section formula and functorial action, not any exactness claim. The quotient/localization identification is written as the actual fraction maps and zero criterion.

2. I read algebra.tex lemma-tensor-localization (00DK), lemma-flat-localization (00HT), lemma-flat (00HD), lemma-Noetherian-permanence (00FN), lemma-completion-tensor/completion-flat (00MA/00MB), and lemma-Noetherian-basic (00IK). The existing localization-module-tensor node supplies the natural localization map; localization-flat and flat-tensor-exact supply exactness, which would not follow merely by citing a flatness definition. localization-noetherian supplies the ring hypothesis for completion-exact-finite-modules. noetherian-submodule-finite supplies kernels/images when an arbitrary finite-module map is factored. The source's Artin–Rees input is encapsulated in the completion-exact theorem, rather than silently reproved here. Localized modules are finite by their displayed generating lists.

3. I read the complete statement and split of lem-per-formal-affine-principal-refinement and checked it has no path back to this item. Its statement gives the completed principal chart, Noetherianity, and canonical restriction. completion-finite-module-tensor gives the natural comparison over R_s. module-completion-complete gives precisely the quotient projections and their kernels. localization-module-tensor identifies the localized finite module. I wrote both inverse fraction formulas for the scalar comparison. This is a routine tensor/quotient calculation, not an uncited formal-scheme equivalence.

4. This step is elementary relative to Step 2: exactness turns the chosen finite generating surjection onto I^nP into the ideal-product image. It then identifies the quotient via an eventually constant tower. No new non-elementary fact, and in particular no exactness of reduction, is used. All ideal powers are finitely generated since the original ideal is, without any extra principal-ideal assumption.

5. The complete principal-refinement statement supplies a chart within every arbitrary open neighbourhood. noetherian-submodule-finite applies over its Noetherian ring C_s, not just over R. The earlier exactness calculation identifies the sheaf kernel with completion of the actual algebraic kernel; finite generators give local finite generation. This verifies the ringed-space coherence definition. Only then do I apply coherent-modules-kernel-cokernel-sum: its statement explicitly allows any ringed space, and supplies finite sums and cokernels. I did not apply the scheme-only 01XZ criterion to T.

6. noetherian-submodule-finite gives finite presentation from a finite generating list. coherent-modules-kernel-cokernel-sum then applies to the finite free sheaves now known coherent by step 5. It does not supply coherence before that has been proved.

7. pqf-def-coherent states local finite generation and finite generation of finite-free kernels. These two clauses directly give the written local finite presentation; this is the elementary proof of modules.tex 01BW, not an unquoted invocation of its conclusion. Principal-refinement permits shrinking to a principal formal chart. Its entries are actual global sections C_s, so Step 2 identifies the matrix cokernel with P-triangle. This step does not claim a global presentation on T.

8. I checked modules.tex 01BO, coherent.tex 01XZ, and the EGA III.1 recall. quasi-coherent-finite-type-affine contains its explicit clause (0) that finitely presented sheaves on a scheme are quasi-coherent; here it is applied only on X_n, an ordinary scheme. The local algebra P/K^nP has a finite presentation by the Noetherian submodule theorem now explicitly cited. The chart quotient ring is Noetherian as a quotient of C_s. pqf-lem-coherent-ft-locnoeth applies to these ordinary quotient schemes, supplying coherence once quasi-coherence and finite type have been checked. Sectionwise inverse limits permit restricting reconstruction to the charts of step 7. The map is the actual quotient projection, so the local equalities prove the canonical reconstruction globally.

9. I read coherent.tex lemma-i-star-equivalence (087T) and lemma-inverse-systems-affine (087W) and the full statements of their existing nodes. closed-immersion-coherent-equivalence is used only for the genuine closed immersions X_n into Spec R, not for the morphism T into Spec R. def-weil-pbc-coherent-formal-module defines the quotient-system category and its transition condition; it is not being cited as an existence theorem. The existing affine theorem provides finiteness, projection kernels, and the inverse functor on systems. The hypothesis R is canonically its completion supplies exactly its scalar identification. The tilde-section theorem identifies the closed pushforward of each quotient tilde sheaf as an ordinary R-module tilde sheaf. Sectionwise limits identify M with the requested global sections, including its actual R-action.

10. The existing affine theorem states an equivalence of categories, hence its clause includes compatible maps, not merely objects. finite-module-complete-over-complete-noetherian identifies both original finite modules with their limits by the residue maps. The uniqueness part of the sheaf limit, supplied by def-pur-sheaf-inverse-limit, then proves equality of the actual sheaf map and the completed module map. Naturality is checked at each coordinate and the unit is explicitly the residue map; nothing is transported through an unspecified equivalence.

11. I read sites-modules.tex lemma-tensor-commute-colimits (03EP) and algebra.tex lemma-tensor-product-exact (00DF). independent-sheaf-tensor-colimits applies to arbitrary commutative ring sheaves on the small open site, so supplies preservation of the finite cokernel and sums needed here; it has no constant-coefficient or ordinary-scheme restriction. tensor-right-exact supplies the algebraic cokernel. The two presentations have exactly the same matrix, which proves the canonical comparison and its multiplication formula. This avoids the false general principle that tensor commutes with infinite limits. coherent-modules-kernel-cokernel-sum supplies the compatibility of coherent exactness with ambient kernels/cokernels.

I checked B1–B10: no new unsplit nodes, all objects in the retained statement are introduced, all notions have dependencies or inline meanings, mathematical formulas use single TeX backslashes after JSON decoding, source tags were checked, actual searches only, and no attachment is claimed for a quotient-system theorem. I checked C1–C8: every non-elementary external input has a node, every citation is to a statement rather than its proof, no dependency reaches the item, and generic off-unit tools are requested in split_report.tool_uses. I checked D1–D5: the steps supply the sheaf/system bridge explicitly, no clause is offloaded to a new node, and no circular reconstruction is assumed. I checked E1–E7: all completion arguments have Noetherian finite-module hypotheses, principal charts have the needed completeness, quotient schemes have their actual quotient rings, and maps/naturality are fixed on residue projections and fractions.

Small cases checked: K=0 recovers the ordinary affine correspondence with constant quotient towers; nilpotent K also gives eventually constant towers, without requiring K nonzero or nonnilpotent. R=0 permits only the zero finite module and gives the empty formal spectrum, consistent with the equivalence. K=R together with completeness forces R=0. For s=0 the principal open and localized section modules vanish; for s=1 the section formula is finite-module completeness. Zero modules, empty finite free presentations and empty opens cause no exceptions. The example R=k[[t]], K=(t), and the sequence multiplication by t with cokernel k checks why one must use exact completion rather than claim reductions are exact. No statement dispute was found.

All steps are shorter than 2000 characters. The local presentations, quotient identities, and fraction maps are routine calculations from the already-cited statements; none hides a separate standard theorem. The substantial global effectivity theorem is the existing 087W node.

## Unfinished work

No stage-1 mathematical work remains. EGA I is wanted as the original historical reference, not as an unstated dependency: the proof here supplies the missing formal ringed-space arguments from the available Stacks tools. No Lean was written, no compiler/Lake/build tool was run, and no repository or launcher file was edited.

## Validation

The preliminary srvcheck.py check_dag exited 0: "check_dag OK: no finding introduced by the sandbox or on its nodes". The required deliver.py --no-push invocation exited 0: "OK (not pushed) deliver/NV/lem-per-noetherian-formal-affine-coherent-modules at 9e956173d2f: preflight passed". The complete server preflight includes check_dag.py and review_split.py. The direct push invocation follows this passing dry run; no mathematical or node-file changes were made after it.

