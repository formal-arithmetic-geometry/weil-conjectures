## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-affine-hc0.json`: item, statement, split; retains the statement and replaces its imported paragraph with five complete steps.
- `dag/nodes/sec-purity-real-sheaves/lem-a1-degree-zero-compact-support-sections.json`: one new statement-only, unsplit node; no Mathlib match. It isolates the degree-zero proper-support comparison, explicitly including comparison of the completed pro-etale/rationalized coefficient model with ordinary lisse adic sections.
- `citations.json`: one verbatim statement quotation for each node cited by each item step.
- `searches.jsonl`: actual msearch records; unavailable LeanSearch requests are marked unavailable in the nodes. `scratch/` retains the sources extracted to text, searches and the writing script.

## Attachments

No attachment for the item. In the current read-only slopmaster2 checkout, `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_zero` is at `WeilConjectures/WeilSheaf/Curve.lean:51` and its proof is `sorry` at line 56. Searches by blueprint id and by compact-support/lisse notions found no finished declaration stating the whole item.

The existing attachment `AlgebraicGeometry.isFinite_of_isProper_of_isAffine` belongs to `lem-sc-proper-affine-finite`; its current source at `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/Proper.lean:91` proves both finiteness and dimension at most zero. I reuse that existing node, without editing it or claiming it attaches the item.

## WANTED

None. The Milne and Bhatt–Scholze PDFs and the required Stacks TeX are already in `literature/`.

## Corrections and observations

The statement is correct, including for the zero sheaf. No mathematical weakening or statement dispute was needed. The finite field, prime-to-characteristic coefficients and pure dimension-one meaning of curve are the chapter's existing conventions. I replaced the statement dependency on the category of Weil complexes alone with the actual Weil-sheaf definition, lisse-adic definition and chapter curve conventions.

The imported proof cited only `def-weil-pbc-constructible-complexes`, whose statement defines finite-coefficient lisse sheaves. That definition neither proves detection of sections at a stalk nor compares it to rational completed coefficients. The corrected proof uses the existing adic fibre-equivalence statement of `cor-galois-lisse-representations`, and leaves the genuinely separate degree-zero/model comparison as one precisely stated dependency. The elementary faithfulness argument is written in the item's step 4, not moved to a new node.

The historical `lean_audit.slopmaster2` refers to a theorem in `AffineCurveUpper.lean` which is absent from this checkout, and to two old sorry-frontier entries. The current source puts this very item directly in `WeilSheaf/Curve.lean` with `sorry`. The listed affine-pushforward finiteness theorem exists but is unrelated to the support argument and cites a prohibited SGA route; I do not introduce a node for that old, unused frontier. The listed affine-curve range node already exists and does not imply vanishing in degree zero. I preserve the audit fields for maintainer reconciliation, rather than replacing them with an unsupported current audit.

The current `main-20261015` item has the same statement; its old master version supplies the support proof. The chapter and unit route are retained: this item supplies the `H_c^0=0` input in the first Rankin–Selberg step. The unit key node is `lem-rp-upper-bound`, so this delivery does not edit its realized fields.

## Unfinished

The single new comparison node is intentionally unsplit, as required for a one-level split. It does not assert the item's vanishing conclusion. On a proper smooth variety its map can have nonzero image; the item's connected affine dimension-one contradiction still has to be carried by the item's steps.

For its later split, the intended argument starts from the compactification formula of Milne Definition 18.1. Degree-zero cohomology is sections of extension by zero; restriction into ordinary sections is injective and boundary-zero sections have proper support in the proper compactification. Transport the integral finite-level construction through the derived-complete realization, rationalization and common finite stages. Bhatt–Scholze Lemma 6.8.2 and Propositions 6.8.4 and 6.8.14 identify the coefficient and constructible realizations, while Remark 6.8.15 identifies the operations. This comparison is part of the new theorem's statement, so it is not silently inferred from a definition. Smoothness ensures that the usual lisse adic category applies. This explanation belongs here, not as a hidden proof in the statement-only child.

## Not duplicates

`lem-a1-degree-zero-compact-support-sections` vs `d-real-cohom` and `sk-d-real-cohom`: those define derived ordinary and compact-support cohomology; they do not assert the injective degree-zero comparison or its proper-support image in the completed coefficient model.

`lem-a1-degree-zero-compact-support-sections` vs `def-weil-ordinary-compact-cohomology`: that is the defining cohomology construction, not the theorem identifying degree zero with ordinary lisse sections and proper support.

`lem-a1-degree-zero-compact-support-sections` vs `def-cbc-etale-section-proper-support`: that defines proper support for a section of an ordinary etale module sheaf; it states no adic realization or degree-zero comparison.

`lem-a1-degree-zero-compact-support-sections` vs `p-real-sections`: that identifies ordinary sections with invariant vectors on a curve; it does not compare compact supports or the completed coefficient model. The existing, stronger-for-fibres equivalence `cor-galois-lisse-representations` is reused for detection; I created no new rigidity node.

`lem-a1-degree-zero-compact-support-sections` vs `lem-pod-compact-support-finite-coefficient-comparison`: that injects constant-coefficient cohomology into a scalar-extended product of finite-level groups in any degree; it does not identify sections of a variable lisse sheaf or give their proper support.

Whole-DAG statement searches and blueprint_refs searches for proper/support/sections, degree-zero/support, lisse/stalk/faithful and nonproper were read. No exact existing comparison was found. The child has no Stacks tag shared with an existing theorem. Stacks Tags 04FS/04FT were read for the support convention, but I do not misattribute the adic comparison theorem to these finite-site support statements.

## Review by Q128

I read delivery-errors B–E in full and checked the actual statements of every cited node against its use. I read the item's old and current blueprint text, its chapter and unit, the current Lean `Curve.lean` declaration, Milne Definition 18.1 on printed pages 118–119 and Remark 29.7 on printed page 166, and Bhatt–Scholze §§6.8 and 7.4. For the new comparison node I read Lemma 6.8.2, Proposition 6.8.4, Proposition 6.8.14 and Remark 6.8.15: the realization assertion is an explicit part of that unsplit theorem and not an assumed equivalence. No SGA source is used.

Step 1 uses `d-real-setup` for the finite-field, nonempty geometrically connected curve conventions, `def-pc-geometrically-irreducible` for the actual quantification over field extensions in geometric connectedness, and `lem-weil-pbc-finite-type-algebra-noetherian` for the Noetherian finite-type algebra. I read the latter's Stacks Tag 00FN, `algebra.tex`, `lemma-Noetherian-permanence`. The affine base-change algebra, finite generators and surjective diagonal multiplication map are written out, rather than assuming base-change permanence without explanation. A field is Noetherian by its two ideals. The resulting affine Noetherian spectrum is both locally Noetherian and quasi-compact.

Step 2 uses clause (1) of `lem-sbc-smooth-relative-dimension-permanence`, not its composition assertion; its statement allows an arbitrary base change. I read Stacks Tags 01VB and 02NK in `morphisms.tex`. The nonempty hypothesis of `lem-sbc-smooth-fixed-dimension-over-field` is supplied in step 1; I read its current project declaration `topologicalKrullDim_eq_of_smoothOfRelativeDimension` at Smooth.lean:286. `sbc-lem-smooth-geometrically-reduced` states geometrically reduced fibres, and over Spec(k) its sole fibre is U itself; I read Stacks Tag 056T (`varieties.tex`, `lemma-smooth-geometrically-normal`). `lem-sc-proper-affine-finite` supplies exactly the dimension-zero consequence used for contradiction; its field and affine hypotheses hold and no properness is assumed except temporarily in that contradiction.

Step 3 invokes only the new node: it states injectivity, the actual target Hom category, the completed-model comparison, and the closed proper reduced support. U_0 is smooth separated finite type, and the coefficients have ell different from p. These are exactly its hypotheses. It does not assume the sought vanishing, nor does it require X affine or connected.

Step 4 invokes clause (2) of `cor-galois-lisse-representations`, whose current DAG statement explicitly covers lisse adic sheaves with the inverse-system/rationalized fibre conventions, not only finite coefficients. U is connected, Noetherian and separated, with ell invertible; step 1 and the global datum verify all four hypotheses. The target of step 3 is precisely the ordinary lisse category in that statement, so the comparison between coefficient models is accounted for before using faithfulness. An equivalence is faithful; its map on Hom sends a zero fibre map to zero, hence detects the section morphism. I read Bhatt–Scholze Lemma 7.4.7, Remark 7.4.8 and Lemma 7.4.10 as the independent source of this familiar fibre argument. I use no Frobenius-fixed condition: geometric sections need not be Weil-equivariant.

Step 5 uses the previous conclusions only. Reducedness, verified in step 2, is needed to identify the full reduced induced support with U itself; it is not omitted. Properness of that support would contradict step 2. Injectivity then kills the original c. This is a short contradiction, not a new node.

For B1–B10, the child is statement-only, self-contained with its notions named as dependencies, has proper blueprint ancestry and actual logged searches, and claims no unverified Mathlib match. Queries were read with both phrasings: hits concern structure sheaves, topological compact functions, or generic faithful constant-sheaf functors, not this adic comparison. Rate-limited LeanSearch is recorded unavailable, not absent. For C1–C8, the quotations in citations.json are verbatim portions (the whole statements) and cover all listed uses; off-unit geometry and fibre equivalence are declared as generic tool uses. For D1–D5, the item carries the connectedness/faithfulness/nonproperness argument; the sole child is a reusable comparison, not a renamed vanishing theorem. For E1–E6, I checked prime-to-characteristic coefficients, nonemptiness for dimension, the connectedness needed for one fibre, the Noetherian and separated hypotheses, and the distinction between ordinary sections and Frobenius-fixed sections. No source error in the item's statement was found.

Small cases: the zero sheaf gives only the zero section; on a disconnected scheme a nonzero section could vanish on another component, so connectedness is used explicitly; on a smooth proper connected curve constant sections can survive in H_c^0, so nonproperness is essential; on a zero-dimensional proper affine scheme H_c^0 can be nonzero, so dimension one is essential. The child remains valid on those proper and zero-dimensional examples because it asserts a support comparison rather than vanishing. For empty X its spaces are zero and its support empty. Every proof step is below 2,000 characters; no long-step exemption is needed.
