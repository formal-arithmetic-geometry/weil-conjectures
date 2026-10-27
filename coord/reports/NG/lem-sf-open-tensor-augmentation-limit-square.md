## Files written

- `dag/nodes/sec-six-functors/lem-sf-open-tensor-augmentation-limit-square.json`: item split into four proof steps; statement and all inherited metadata retained. No new nodes and no Mathlib leaves.
- `citations.json`: eight verbatim statement excerpts, covering every node citation of every proof step.
- `searches.jsonl`: five actual Mathlib searches for this item, supplementing its inherited search records.
- `report.md`: this report.

## Attachments

None. Searched the exact blueprint tag and augmentation/limit and tensor/augmentation terminology in `lean/WeilConjectures/`, then the open-tensor, adic, and Roos modules. Existing ordinary open tensor and unrelated augmentation declarations do not state this simultaneous strict-tower square together with its actual tensor-completion units. No compiler or Lake command was used.

## WANTED

None. All source documents used are present locally.

## What needed repair

The item was statement-only, with no proof. Its statement is correct as written and has not changed. Its pre-existing statement dependencies already supply the required notions and construction theorems. In particular, the statement of `lem-sf-open-tensor-quotient-augmentation`, rather than its proof, supplies both constructibility assertions and the simultaneous strict augmentation equality. The statement of `lem-sf-open-roos-extension-comparison` supplies the qcqs hypotheses and the specified signed augmentation comparison. Neither needs to be reproved or restated as a new node.

The unit route was checked in `dag/units/sk-prop-sf-pf-coherence.json`, the chapter record, and the current-brief snapshot `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md`. This split serves the open-factor and finite-reduction compatibility parts of that proof via its existing ancestor chain. No chapter or unit record was changed. No SGA argument is used.

## Unfinished work

Nothing remains for this one-level split. Dependencies may remain unsplit; this delivery assembles their precise statements and does not claim to prove them or the Lean implementation.

## Review by NG

I read Bhatt–Scholze, *The pro-étale topology for schemes*, printed pp.49–50 (PDF pages 49–50), including Definition 6.5.1 and Lemmas 6.5.3–6.5.5 and 6.5.8. Lemma 6.5.5 says that the ordinary derived tensor of two constructible objects is already complete; 6.5.8(2),(3) preserve constructibility under constructible locally closed restriction and extension. For the actual quotient maps, I read the full statements of `lem-fix-constructible-tensor-completion`, `def-sf-tensor-completion-comparison`, and `def-pur-integral-derived-operations`: these specify the finite tensor tower and the actual quotient-augmentation representative, not merely an unspecified isomorphism to a completion. I also read Stacks Tag 09BP (`proetale.tex`, `lemma-j-shriek-limits`), Tag 0GL1 (`sites-cohomology.tex`, `lemma-j-shriek-and-tensor`), and Tag 0940 (`sites-cohomology.tex`, `section-derived-limits`, especially `lemma-derived-limit-is-ok`) to check the background of the existing extension and strict-limit interfaces. The signed normalization is the explicit statement of the cited DAG theorem, an agent refinement of the Stacks construction, and is not attributed verbatim to Stacks.

Step 1 uses exactly the statements of `lem-sf-open-roos-extension-comparison` and `lem-sf-open-tensor-quotient-augmentation`. The former explicitly states that U and X are Noetherian and qcqs and that ell is invertible, for an open immersion of finite-type schemes over the stated finite-field datum. The latter explicitly states that j_!K and j^*P are bounded constructible integral objects. Together with the given K and P, these are all the geometric and input hypotheses of the constructible tensor-completion theorem for the two pairs. I do not infer constructibility solely from exactness or completeness, or assume separatedness.

Step 2 uses `lem-fix-constructible-tensor-completion` for completeness and invertibility and for its canonical quotient map, `def-pur-integral-derived-operations` for the actual targets L_X T and L_U S, and `def-sf-tensor-completion-comparison` for identification with the recorded chi. I checked that both use the same flat-term K-flat finite tensor tower after restriction of scalars, not the ordinary tensor over A_n of un-derived cohomology sheaves. The first Roos coordinates are the quotient tensors and the second are zero. Thus this identifies actual maps, not just isomorphic source and target objects. These three nodes were opened in full before citation.

Step 3 uses the strict simultaneous equality displayed in `lem-sf-open-tensor-quotient-augmentation` and the natural normalized Roos isomorphism and canonical augmentation maps specified by `lem-cbc-exact-product-functor-strict-limit`. The latter explicitly states that theta is natural in the tower and that its canonical augmentation is the signed representative. I wrote out both first coordinates after the tower map and both zero shifted coordinates. Naturality of theta then localizes their equality. Transition compatibility is part of the strict square, so the product map commutes with 1-s and with the original differential, rather than just yielding equal level evaluations. This avoids assuming that evaluation or limit projections are faithful. The elementary product-coordinate check is written inside this step and does not hide an independent comparison lemma.

Step 4 uses the exact equation `lambda_M j_!(a_c) = a_{Jc}` in the statement of `lem-sf-open-roos-extension-comparison`, specialized to M=S and c=c_S. Its hypotheses allow arbitrary strict towers and arbitrary complexes D on U, so H_U need not satisfy any extra boundedness hypothesis for this application. The resulting equation is substituted into step 3 with no change of orientations: both sides go from H to L_X J S. The displayed lambda has the same signed normalization as the item's lambda_S.

The two off-unit statements are declared as generic tools in `split_report.tool_uses`: the constructible tensor-completion theorem and the exact-product strict-limit theorem. They provide completeness and normalized homological algebra within the existing open-factor route; neither replaces a unit step by another geometric argument.

I tested j=id (the strict square reduces to the same quotient augmentation), U empty and K=0 or P=0 (all relevant maps are the unique maps between zero objects), and a constant identity-transition tower (the augmentation is (c,0), and 1-s kills its first coordinate). I also checked torsion coefficients such as R/t as inputs on a point: reductions can have nontrivial Tor and need not be perfect over A_n, but the proof only uses derived reductions and integral constructibility, so it does not impose a forbidden finite-Tor condition over A_n. All four proof steps are shorter than 2000 characters; their combined text is 2117 characters.

For duplicate and leaf checks, I searched the whole imported blueprint using `blueprint_refs.py search` for augmentation, Roos, and tensor/completion, inspected the nearby DAG statements, and checked the blueprint ancestor with `blueprint_refs.py ancestor`. The parent `lem-sf-open-projection-roos-completion` depends on this item and was deliberately not cited. The three already-existing supporting comparison results are reused; no new node restates a clause. Mathlib searches were run through msearch.py, with a second semantic phrasing. The hits concern ordinary module adic completion, shape extension, Dold–Kan, inverse systems of sets, or light condensed monoidal structure. I read `Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean` at lines 74–78, 328–335, and 357–364; none supplies this derived pro-étale augmentation square by one-line specialization. Inherited search entries were preserved, and only searches actually run in this session were appended.

Against delivery-errors B–E: there are no new nodes to be elementary, duplicate, self-referential, or missing searches; every proof citation is checked against its statement and backed by a verbatim excerpt; no proof cites an ancestor; every non-elementary input is a cited statement; all geometric, coefficient and constructibility hypotheses were checked above; and the compatibility of actual connecting data is an explicit signed coordinate equality. No source error or statement dispute was found.
