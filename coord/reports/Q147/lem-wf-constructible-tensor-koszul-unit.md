# Stage-1 delivery: lem-wf-constructible-tensor-koszul-unit

Group Q147, 2026-10-22. Direct delivery under the dispatched brief.

## Files written

- dag/nodes/sec-six-functors/lem-wf-constructible-tensor-koszul-unit.json: statement, split into five proof steps; no Mathlib match.
- citations.json: one verbatim statement quote for each node used by each proof step.
- searches.jsonl: actual msearch results, retained verbatim.

No new nodes, no new Mathlib leaves, no unit or chapter edits. The original statement, source, creation data, blueprint ancestry and existing search records are retained.

## Attachments

None. Searched the upstream WeilConjectures source for the exact blueprint tag, quotient/Koszul completion, and constructible tensor. The tag has no hit. The finite-etale-coefficient theorem AlgebraicGeometry.Etale.constructibleFiniteTor_tensor (SixFunctors/Etale/Derived/Stability/OpenImmersion.lean:103) does not concern this integral completed ring or completion units. The condensed module-object tensor in SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean:494 concerns another coefficient presentation and does not state the comparison and normalization clauses. Neither is an attachment.

## WANTED

None. Read the obtained Bhatt–Scholze paper and local Stacks sources; no SGA source was used.

## Findings and corrections

The item was unsplit and there was no prior saved split or report in this sandbox. No live stage-1 repair note for this id was present. The statement needs no correction. In particular its integral C_E is explicitly the integral category underlying def-wf-weil-category, not that definition's rational category also denoted C_E.

The substantive distinction is between the completion of the ordinary tensor and the tensor of the two reductions. I introduced the existing whole-tower comparison theta from lem-pur-integral-ambient-operation-models to identify their actual quotient augmentations. The cited tensor-completion theorem alone gives a comparison to the completed tensor operation; I did not silently identify its target with Q(T). The quotient/Koszul comparison is taken from the completed-coefficient theorem lem-weil-pbc-constant-completion-equivalence, not from the constant-coefficient Stacks lemma in isolation. Membership of isomorphic objects retains the witness maps and their compatibility explicitly.

## Not duplicates

No new nodes. Searches of the whole DAG and blueprint found the needed existing category-identification, quotient/Koszul comparison, completed tensor constructibility and ambient operation model nodes. In particular lem-ag-uniform-complete-tensor is an existing stronger constructibility result, so creating another tensor-constructibility lemma would duplicate work. The present assembly uses the existing lem-pur-integral-operations-preserve-constructible and then spells out isomorphism transport of the required tower witnesses.

## Mathlib search assessment

Ran msearch leanfinder with two distinct phrasings, leansearch, loogle and grep; all returned successfully. Recorded the exact query strings and the returned declaration names in the item, alongside its inherited search records. LeanFinder found ordinary algebraic AdicCompletion tensor results; LeanSearch found ordinary module sheaf units and unrelated statements; grep for derived completion/Koszul tensor had no hits. Read Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean around line 74: ofTensorProduct_naturality is naturality of an ordinary linear map, not the derived-sheaf Koszul completion unit. The second phrasing returned light condensed monoidal structures and local cohomology, not this theorem. No match or unavailable result was invented.

## Review by Q147

I read coord/delivery-errors.md B–E in both copies, the chapter and unit, the current blueprint proof of fix-prop-projection-formula, and the source statements of every node in proof. I read Bhatt–Scholze Definition 6.5.1, Lemmas 6.5.3–6.5.5 and the actual argument on printed pages 49–50: tensor closure and completeness concern completed ring coefficients. I read Stacks proetale.tex Tag 099L (section-derived-completion-noetherian) and Tag 099M (lemma-naive-completion), and algebraization.tex Tag 0A0E (lemma-derived-completion-koszul). The former explicitly identifies complete constant and completed-coefficient categories; the latter uses the Koszul complex in degrees [-r,0]. These justify the route of the existing comparison nodes. There are no new nodes needing independent sources.

Step 1 uses the full statements of lem-pod-separated-finite-type-base-change, lem-weil-pbc-qcqs-over-affine, lem-weil-pbc-finite-type-over-noetherian and lem-kun-dimension-finite-type to check the hypotheses on W. A field is noetherian because its ideals are 0 and 1; ell is invertible because p and ell differ. The last category-identification sentence of lem-weil-pbc-integral-stratified-perfect-characterization explicitly says both categories coincide with the same ring sheaf and reduction functors. Reading def-wf-weil-category verifies which integral category underlies its rationalization. This avoids taking category coincidence merely from similar notation.

Step 2 uses precisely the whole strict tower and augmentation assertion of lem-pur-integral-ambient-operation-models, including its zero shifted-product coordinate and invariance under changes of K-flat representatives. The balanced tensor map and its inverse are written. The qcqs and invertibility-of-ell hypotheses of lem-fix-constructible-tensor-completion were checked in step 1. That node explicitly states invertibility of its actual quotient-tower comparison, so composing with theta inverse proves invertibility of the unit into Q(T).

Step 3 reads the last paragraph of lem-weil-pbc-constant-completion-equivalence, which states the Koszul/quotient comparison respects units for completed coefficients as well as constant coefficients. Specialization is to the same B and principal generator varpi. def-weil-pbc-intrinsic-completion specifies exactly the Koszul transitions and mapping-fibre unit c maps to (u(c),0). Functoriality of the derived limit comes from the exact functor stated in lem-weil-pbc-ringed-strict-tower-homotopy-limit. The induced comparison commutes with h tensor 1 before deriving and therefore after deriving. Inverting this comparison gives rho in the requested direction and rho chi = eta; no arbitrary object isomorphism is substituted for a specified unit.

Step 4 uses clause 2 of lem-pur-integral-operations-preserve-constructible, which explicitly places the completed tensor in its integral constructible category. The category identification in step 1 applies. I opened def-weil-pbc-bounded-constructible-complete and def-weil-pbc-bounded-constructible-tower, and wrote how each etale witness and local model comparison is carried along the reductions e_n of an isomorphism. The displayed compatibility square supplies the normalization and preserves the cocycle; bounds and models do not change. Naturality in lem-weil-pbc-ringed-koszul-completion-reflector transfers intrinsic completeness. This establishes membership for T and C(T), including the uniform and compatible data, not just levelwise cohomology constructibility.

Step 5 specializes the reflector's natural unit to h = f tensor g and checks that this is the explicit intrinsic unit using its product mapping-fibre formula. Both directions of the naturality equation have domain T_{M,N} and codomain C(T_{M',N'}). Arbitrary arrows, including zero arrows, are allowed. The naturality statement is already on the derived category; the chain calculation fixes the normalization and is not a claim that arbitrary derived arrows have chosen strict representatives.

I checked B1–B10: no new statement-only node or duplicate is introduced, the inherited statement is self-contained with its notion dependencies, TeX has single mathematical escapes, existing fields are retained, and no Mathlib leaf or unsupported attachment is claimed. For C1–C8, every non-elementary input is a cited statement; citations.json is generated from those statements and checked by substring containment. The geometric and completion tools from other units are declared in split_report.tool_uses, with their role; the unit has no proof steps whose route this replaces. I checked dependency reachability for the principal comparison and constructibility tools and found no path back to the item. For D1–D5 the five steps supply the identifications, invertibility arguments and witness transport instead of moving the conclusion to a new lemma. For E1–E7, I checked the coefficient ring, principal ideal, finite-type geometry and map directions; there is no statement dispute or source correction.

Small cases: W empty gives the zero derived category and the unique units; M=0 or N=0 gives the zero tower and zero mapping fibre; M=N=B checks that rho carries the coefficient quotient map to the degree-zero Koszul inclusion. Torsion M or N is not assumed flat: the cited ordinary derived tensor is computed on flat-term K-flat representatives. The arrows f or g may be zero or non-invertible. No denominator, Frobenius or rational-descent claim is smuggled into this integral item. All proof steps are under 2000 characters, so none hides a long auxiliary comparison.

## Unfinished work

None in this one-level split. Existing cited nodes retain their own independent proof obligations. No Lean was written, no compiler or Lake/build command was run, and no repository or launcher file was edited.
