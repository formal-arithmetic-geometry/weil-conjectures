# Worker report: lem-pur-sequence-pullback-tensor-cochain

Group NG, stage 1, 2026-10-27. No Lean files, compiler, Lake build, repository files, or launcher files were modified.

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-sequence-pullback-tensor-cochain.json`: the live statement is unchanged and now has six proof steps; it is not a Mathlib leaf.
- `citations.json`: 18 verbatim statement quotes covering every proof citation.
- `searches.jsonl`: the six additional Mathlib-search records from the earlier NO attempt, retained with their original timestamps and attribution. The five searches already present in the live item were retained unchanged.
- No new nodes or Mathlib leaves.

## Attachments

None. The live `lean/WeilConjectures/` search found no declaration carrying this blueprint tag or the exact declaration name. The node metadata names `WeilConjectures.pullbackTensorSequenceCochain_existsUnique` in `Sheaf.Paper.CompletedPullbackTowerRealizations`, but that source file is absent from this read clone; it is therefore not a completed project declaration and is not attached.

## WANTED

None.

## What was wrong and what changed

The inherited item had an empty proof and only the shorthand argument that ordinary pullback/tensor comparison, totalization, and generators suffice. I revalidated and reused the prior NO expansion into six checkable steps: sequence-site continuity and representable flatness; the specified-adjunction module tensorator and its unit formula; preservation of the integer diagonal coproducts and the total-complex comparison; the signed differential and naturality calculation; the displayed unit/summand normalization; and uniqueness by adjunction transpose, sheafification, pure-tensor generation, and coproduct extensionality. The old retained argument and its provenance remain in `split_report.retained_arguments`; its unrelated K-flat-resolution citations are not used by the new proof. The two generic tools are declared in `split_report.tool_uses`.

There are no new/existing node pairs, so the duplicate audit is vacuous.

## Review by NG

I read the live item, its chapter and unit records, the latest blueprint chapter association, and delivery-error checks B--E. The prescribed archive glob returned no archived directories. I also read the earlier NO sandbox evidence for this item and compared its statement byte-for-byte with the live repository node before reusing its proof and search records; those original search records are retained unchanged in `searches.jsonl` and attributed to NO here and in `split_report.evidence_provenance` and are not presented as searches run by NG. The current Lean read clone contains no exact completed declaration, and the candidate metadata is not evidence of a finished proof.

For step 1, I checked that the sequence topology is vertical-slice coverage and that the pro-etale inverse-image functor preserves terminal objects and pullbacks. The product of the pro-etale comma category with the natural-number identity-arrow category supplies finite cones, including the empty diagram, so the representable-flatness check does not assume a terminal object for the whole sequence site.

For step 2, I checked the actual constant-section coefficient map and the specified additive adjunction (F_f\dashv f^s_*) from the integral comparison node. The cited ordinary ringed-site tensor theorem supplies a natural isomorphism on module sheaves and the exact adjunction-unit pure-tensor equation. No finite-level evaluation isomorphism or geometric finiteness hypothesis is substituted.

For step 3, I checked the signed total definition, the existence of every integer diagonal coproduct, the left-adjoint colimit preservation statement, and the cited totalization isomorphism with its summand equation. The argument therefore covers unbounded complexes and does not introduce finite-diagonal or boundedness assumptions.

For step 4, I wrote both differential naturality equations and retained the ((-1)^p) sign in the second summand. The direct sum of the component tensorators and of their inverses gives mutually inverse chain maps, and the same equations give bifunctorial naturality.

For step 5, I checked that the unit is applied to the total-summand inclusion, then substituted the summand identity and the module pure-tensor formula. This yields exactly the displayed (g_{p,q,k,b_fV}) formula at every integer degree and every quotient/site object, including (n=0).

For step 6, I checked the transpose under the specified adjunction, the presheaf tensor unit, pure-tensor generation of the algebraic tensor product, the sheafification uniqueness property, and the coproduct universal property. These imply equality on each tensor summand and then on every total degree; injectivity of the adjunction bijection proves uniqueness of the entire natural cochain isomorphism. I also checked zero complexes, degree-zero and negative-degree inputs, complexes nonzero in every degree, empty sites, and non-flat terms. No hidden K-flat or constructibility assumption is used, and every citation quote is a verbatim substring of its node statement.
 
## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.


## Source and search-result verification

I read Stacks sites-modules.tex Tag 03EL (lemma-tensor-product-pullback), including its bilinear-adjunction proof, Tag 03CY (lemma-sheafification-presheaf-modules), sites-cohomology.tex Tag 07A4 (lemma-pullback-tensor-product), proetale.tex Tag 09A5 (section-morphism), categories.tex Tag 0038 (lemma-adjoint-exact), and algebra.tex Tag 00CX (lemma-tensor-product). The ordinary final total-complex map of 07A4 is the comparison assembled here; its preliminary derived K-flat replacements are unnecessary for this ordinary assertion. I read TotalComplexMap.lean mapTotalXIso, its summand equations, mapTotalIso and both naturality equations. I inspected the prior search hits in Mathlib PullbackContinuous.lean, PullbackFree.lean and Algebra/Homology/Monoidal.lean: they give the module adjunction, free-module normalization and complex tensor infrastructure, but do not state this specified whole-sequence cochain existence and uniqueness theorem. No Mathlib match is asserted. The first server review_split passed, and the initial required dry run exited successfully at 95e217b764a; the final dry run below will cover these provenance/report corrections.
