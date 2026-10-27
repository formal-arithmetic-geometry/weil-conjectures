# Stage-1 report: lem-sfb-topos-naive-cotangent-pullback

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-topos-naive-cotangent-pullback.json: existing statement, now split into five steps; no Mathlib match. Its statement, statement dependencies, source and inherited blueprint ancestry are unchanged.
- citations.json: verbatim statement extracts for all 16 proof-step citations.
- report.md: this report. The existing searches.jsonl was read and retained; its six genuine Q158 searches have been added to the item's inherited search records without repeating the searches.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched lean/WeilConjectures both for the exact blueprint tag and for naive cotangent terminology. The project hits concern ring presentations, localizations, smoothness or the symmetric algebra; none states this comparison for arbitrary geometric inverse image of ring sheaves. In particular the ring-theoretic declarations are not attachments of a sheaf/topos statement.

## WANTED

None. All source documents used are present in literature/stacks-project/.

## Findings and changes

The item was an unsplit, proof-empty statement of Stacks Tag 08TZ. Stacks omits the proof and only points to 08TQ, so merely citing that hint would leave the evaluation ideal, its square, and the differential square unjustified. The split now gives those arguments. The statement agrees with 08TZ interpreted through the standard two-term representative already specified by the item and by 08TY; no statement dispute or correction is needed.

The necessary lemmas already exist. I reused the polynomial-algebra clause of lem-trf-geometric-standard-differential-comparison (rather than creating a new polynomial lemma), lem-trf-topos-inverse-image-differentials, lem-trf-geometric-inverse-image-exact, and lem-pur-independent-inverse-image-tensor-comparison. The ideal-square calculation uses the existing sheaf tensor definition, bilinear universal property and local representation of sheafification. Exactness preserves images by their kernel-of-cokernel formula; this short inference stays in the item's proof. The final differential-square and localization calculations also stay in the item. There is no restatement of the item's conclusion in a new node.

The six Q158 searches already logged were read: LeanFinder under two phrasings, Loogle, two Mathlib greps (Algebra/Category and RingTheory) and LeanSearch. Source inspection covered Mathlib/RingTheory/Extension/Cotangent/Basic.lean (especially cotangentComplex, cotangentComplex_mk and the presentation maps), RingTheory/Extension/ExtendScalars.lean, Algebra/Category/ModuleCat/Differentials/Presheaf.lean and Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean. The hits are ring-level or concern a different sheaf construction and do not give a one-line specialization to the item. All six searches succeeded; none is recorded as unavailable. Inherited searches from the item's creator are preserved as inherited records, not represented as searches newly run by Q158.

I read the chapter/unit records and the latest blueprint files sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. This supplies the general topos input in the item's inherited Tag 0D0W prerequisite chain, without changing a chapter or unit route. The inherited blueprint.from.node is null (blueprint_refs.py ancestor prints None); I did not edit maintainer-owned ancestry. Whole-blueprint searches for cotangent, naive cotangent, conormal and polynomial algebra found no equivalent imported statement. Generic tools of other units are individually declared in split_report.tool_uses, with the precise clause used; no unit theorem is replaced by a different route.

## Not duplicates

No new nodes were created. Existing nodes were reused in place of possible new exactness, polynomial, differential, tensor, local representation and bilinear-universal-property nodes. The two-term conormal comparison is not a duplicate of the full simplicial comparison: the latter supplies its polynomial-algebra clause, while the ideal square, quotient and differential square are proved here.

## Review by Q158

I read Stacks sites-modules.tex at lemma-pullback-NL (08TZ) and its hint to lemma-pullback-differentials (08TQ), including the displayed relation-map proof. I also read the standard presentation in lemma-NL-up-to-qis (08TY), the tensor definition 03EK and lemma-tensor-product-pullback (03EL), and lemma-flat-pullback-exact (04JC). In cotangent.tex I read the free/forgetful square in lemma-pullback-cotangent-morphism-topoi (08SV). I checked the local sheafification statement of the existing 00WK node. There are no new nodes requiring further source review. The omitted portion of 08TZ is explicitly an agent-written expansion of its hint, as recorded in proof_origin.

For step 1 I opened lem-trf-geometric-standard-differential-comparison and lem-trf-geometric-inverse-image-exact. The former actually states preservation of the polynomial algebra, coefficients, variables and evaluation counit; I only use that clause, not a truncation comparison it does not state. The latter states exactness on transported modules, so it identifies the evaluation kernel with the target kernel. The geometric morphism orientation is correct: u is Sh(C) to Sh(D), hence F carries sheaves on D to sheaves on C. Both sites are in the specified common sheaf universe.

For step 2 I opened all five cited statements. lem-pc-sites-sheaf-tensor-bilinear-universal constructs multiplication from its bilinear map; def-pur-sheaf-tensor-product states that this tensor is sheafified sectionwise tensor; lem-weil-pbc-site-sheafification-sections-local supplies local representation of a sheafified section. Together these identify the image of multiplication with exactly the locally generated ideal square, not merely with sectionwise products. lem-pur-independent-inverse-image-tensor-comparison states the pure-tensor normalization for the algebraic inverse-image lift with transported coefficients, so the multiplication morphisms correspond. Exactness from lem-trf-geometric-inverse-image-exact then preserves this image. There is no scalar extension along an unrelated coefficient map, and no flatness hypothesis is introduced. Preservation of images is explained by ker(coker), not imported without a citation.

For step 3 the exactness statement gives preservation of the quotient cokernel, and lem-sfb-sheaf-polynomial-cotangent-comparison gives precisely the definitions of J, J squared, the quotient and the standard two-term model. I checked B-linearity by the fact that J acts trivially modulo J squared and by the evaluation comparison. This is the elementary consequence of these cited statements written out in the step, with no independent lemma hidden.

For step 4 I checked lem-trf-topos-inverse-image-differentials: it states the sheaf differential isomorphism with universal derivations, which is what the step needs for A to P. The ordinary tensor comparison applies to two P-module sheaves, Omega and B, with transported ring FP. It states the normalization on generalized pure tensors needed here. The B-prime action is on the second tensor factor. This is not an invocation of a derived tensor comparison, nor an assumption that the conormal module is flat.

For step 5 I checked the differential formula in lem-sfb-sheaf-polynomial-cotangent-comparison, the universal-derivation clause of the differential comparison, the pure-tensor clause of the tensor comparison, the epimorphism preservation supplied by exactness, and the localization functor in def-weil-abstract-derived-category. The displayed calculation is made before precomposing with the quotient epi and then cancelled. Thus it proves an actual chain isomorphism and its image in D, rather than assuming an identification from equal cohomology groups. The final statement's canonical comparisons are exactly those constructed in steps 1-4. I copied the relevant parts of every cited statement into citations.json, and each extract really contains the assertion used.

I checked B-E of delivery-errors.md against this result. B: there are no new statement-only nodes to typecheck or search; the item retains valid TeX, its source and the maintained notion dependencies. C: every non-elementary input is one of the opened cited statements; short consequences of exactness and of the localization definition are written explicitly. No proof of a cited node is used as an extra unstated interface. I traversed the dependency closures of the polynomial, differential, tensor, exactness, bilinear and local-representation nodes: none reaches this item, so these uses do not close a cycle. D: five steps carry the proof, with zero new nodes; the source's omitted argument is supplied. E: no pointwise section surjectivity, enough-points hypothesis, flat base change or affine assumption occurs. I tested identity inverse image, component projection from a product topos (each construction is componentwise), and the degenerate empty topos, where all module sheaves and both complexes vanish. Zero rings and nonflat maps such as Z to Z/4 cause no change: only transported module inverse image is used, which is exact independently of that ring map. These checks give no counterexample. All steps are below 2000 characters, and the final assembly consists of the explicit differential equality and formal localization, with no hidden non-elementary lemma.

## Unfinished work

None in the authorized split. The reused statements keep their own proof states; this delivery does not claim their Lean proofs are finished. Validation and delivery results follow below when available.
