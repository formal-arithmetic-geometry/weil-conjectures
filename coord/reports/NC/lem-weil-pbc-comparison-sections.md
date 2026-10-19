# Stage 1 report: lem-weil-pbc-comparison-sections

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-comparison-sections.json` — statement, split into two proof steps; no new nodes.
- `citations.json` — verbatim statement excerpts for every cited node in both steps.

## Attachments

No attachment: the source contains comparison-continuity declarations, but none states the full imported item including the explicit affine basis formula and the sheaf-of-sets clause as one declaration.

## WANTED

None.

## Problems and corrections

The imported proof had `uses_not_cited` entries for finite-presentation descent, section continuity, and ind-etale stability. I checked those nodes in the DAG and added them to the relevant steps. The imported second paragraph also used the inverse-image definition without citing it; that citation is now explicit. The statement itself agrees with the blueprint paragraph and was not weakened or strengthened. Mathlib searches were run for the item (LeanFinder, Loogle, and grep, each with a second phrasing); they found only general affine-limit or sheaf infrastructure and no declaration of this comparison formula.

## Review by NC

I read the item source `literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/lem-weil-pbc-comparison-sections.md`, including both proof paragraphs, and compared every hypothesis with the imported statement: affine base, affine etale finite-presentation stages, etale module sheaf, natural section identification, and the separate sets assertion. I also searched both read-only Lean trees for the blueprint tag and comparison-section names. The existing source theorem `AlgebraicGeometry.ProEtale.isColimit_comparisonUpperStar_mapCocone` is a closed general comparison-continuity result, but it does not itself state the item's displayed section formula or the sets extension, so I did not attach it.

For step 1, I opened `def-weil-pbc-cover-cech`, `lem-weil-pbc-ind-etale-basis`, `lem-weil-pbc-etale-finite-data-descent`, `lem-weil-pbc-etale-section-continuity`, and `lem-weil-pbc-ind-etale-stability`. The Cech node supplies the finite-cover complex and fibre-product terms; the basis node supplies finite basis refinements and restriction-detects-sheaves; finite-data descent supplies stage descent of finite-presentation objects; section continuity supplies the filtered-colimit section isomorphism; and ind-etale stability supplies base-change and composition stability for the presentations. Those are exactly the non-elementary facts used in constructing `P_F` and checking its equalizer. The remaining passage from finite products and kernels to the equalizer is the standard finite-limit calculation in modules, and the same calculation for sets is the final elementary observation in the paragraph.

For step 2, I opened `def-weil-pbc-site-comparison-morphism`, `def-weil-pbc-inverse-image`, and again the finite-data and section-continuity nodes. The comparison-morphism node states the relevant geometric adjunction; the inverse-image node states that inverse image is the left adjoint to direct image; finite-data descent gives factorization of maps from an inverse limit through a finite stage and eventual equality; and section continuity gives stage representatives. Thus the two constructions are inverse by their stated adjunction data, not by an unstated derived-category comparison. The hypotheses needed for the continuity invocation (affine transitions and qcqs finite-presentation stages) are verified from the item's affine finite-presentation basis description; the basis sheaf extension supplies the arbitrary pro-etale object case.

I tested the edge cases conceptually: a terminal stage gives the identity colimit map, an empty section set is preserved by the set-valued equalizer argument, and a finite cover with one member reduces to the ordinary restriction map. No new statement was introduced, so there were no additional small-case claims to test. I corrected only the dependency accounting and blueprint provenance, then recorded exact quotes in `citations.json`.

## What remains

Nothing remains for this stage; the sandbox is ready for the required dry run.

## Second reading by NC

- Item statement: checked the affine-base, ind-etale presentation, module and sets clauses against the named blueprint file, statement and both proof paragraphs; unchanged in mathematical content. Normalized literal escaped newlines and doubled TeX escapes so the displayed statement renders once.
- Step 1: checked every cited statement against the actual affine systems. The abelian continuity node only covers abelian sheaves, so added the existing sets continuity node. Checked its source against etale-cohomology.tex, theorem-colimit (09YQ), lines 7400ff, and sites.tex, lemma-compute-pullback-to-limit (0A35), lines 3859ff: the latter supplies the set-valued degree-zero formulation, rather than claiming 09YQ literally states a sets theorem. Added both existing etale restriction nodes (03S2, section-extension-by-zero, etale-cohomology.tex lines 11399ff). The ind-etale stability statement explicitly covers arbitrary maps between two ind-etale algebras; the definition supplies their presentations. Expanded the finite-stage covering, fibre-product limit and finite equalizer arguments, including the empty covering. Verdict: repaired C1/C4/E5; the section comparison is now valid for both coefficient categories.
- Step 2: finite-data descent only concerns morphisms between etale finite-presentation objects descended by base change; it does not state the factorization from an arbitrary limit used here. Replaced that citation by the existing Mathlib leaf lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit. Read its declaration RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit at Mathlib/Algebra/Category/Ring/FinitePresentation.lean:81 and Algebra 00QO (lemma-characterize-finite-presentation), algebra.tex lines 31886ff. Wrote eventual equality on finitely many generators, the restriction square for a general basis map, independence of presentation, and the two inverse adjunction constructions. Added lem-weil-pbc-affine-etale-site-topos for extension from the affine etale basis (04HR), and checked the finite-presentation condition using affine X. Verdict: repaired C3/C4/E5 without changing the blueprint route.
- New nodes: none; there is no new-node statement, duplicate, elementary lemma or Mathlib-leaf decision to audit. All added citations reuse existing nodes. Traced their statement/proof dependency closures: none leads back to this item. Generic continuity/restriction/basis tools from other units are declared in split_report.tool_uses for the maintainer to judge.

Changes: replaced an inapplicable finite-data-descent citation; supplied the missing sets continuity and restriction inputs; expanded finite-limit and naturality calculations; repaired statement rendering and refreshed every citation with a verbatim statement. The first worker's review is retained above as requested; its claims about the finite-data citation and the sets extension are superseded by this reading.

Small cases: zero module sheaf gives zero groups at every stage; terminal presentation gives ordinary etale restriction; over a field the affine algebra factorization is still the same finite-generator argument; empty U has singleton set sections and zero module sections, including the empty cover; a one-member cover gives the ordinary sheaf equalizer. No statement dispute or added hypothesis was needed. No Lean was written and no compiler, Lake or build tool was run.
