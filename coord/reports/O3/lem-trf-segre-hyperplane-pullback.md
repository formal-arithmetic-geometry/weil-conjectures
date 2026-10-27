# Stage-1 report: lem-trf-segre-hyperplane-pullback

## Files written

- dag/nodes/sec-trace-formula/lem-trf-segre-hyperplane-pullback.json: statement, split; Mathlib verdict no match. Statement unchanged; four proof steps, all using existing nodes.
- citations.json: verbatim statement excerpts for every step/node citation.
- searches.jsonl: actual search-command results, including a second semantic phrasing.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. The prior candidate AlgebraicGeometry.ProjectiveSpace.nonempty_twistRestrict_segre_iso (lean/WeilConjectures/AlgebraicGeometry/ProjectiveSpace/SegreTwist.lean:115) is retained as history, not attached. Its base-change projective spaces and integral-model twists do not themselves give the relative-Proj/affine-local twist comparison required by this node. Read its declaration and coordinate-transition proof; obeyed the explicit rejection and did not submit ATTACH again.

## WANTED

None.

## Audit and changes

The item was unsplit and the sandbox contained no node/report. Copied the current live node, preserving its statement, earlier Mathlib searches, Lean candidate, source, and blueprint ancestry. Read GOAL.md, the chapter and unit records, the current blueprint's local-term proof, and the listed contract documents. This auxiliary node realizes the previously recorded relative-ampleness/Segre subargument below the blueprint ancestor; it does not replace the local-term unit route.

Read Stacks constructions.tex, Tag 01WD (lemma-segre-embedding), which constructs Segre from the invertible module pr_1^*O(1) tensor pr_2^*O(1) and the products of coordinate sections. Read Tag 01NE (lemma-projective-space) and its following paragraph, Tag 01OA (section-projective-bundle) with its quotient discussion, and Tag 01OE (lemma-projective-space-bundle). In particular, the source's relative-Proj pullback characterization is not inferred from the rejected Lean candidate. The existing generic projective-bundle nodes explicitly state the identifications with the relative-Proj free-module projective space and the affine degree-one twist.

Searched the whole DAG for Segre, generating sections, projective-space quotient/twist statements, and the source tags 01WD/01NE/01O9/01O4/01NA. Blueprint-ref searches for Segre, projective space, generating sections, hyperplane, and O(1,1) found no duplicate supplying this precise statement. lem-chow-segre states closed immersion and a very-ampleness consequence; it does not state this module isomorphism. The needed intermediate general theorems already exist, so no new lemma nodes are justified.

Mathlib searches were run through msearch.py with leanfinder, loogle, grep, and leansearch, then a second leanfinder phrasing. Read the returned signatures: pullbackSpecIso is a scheme fibre-product calculation; Proj.pullbackAwayιIso is the intersection of Proj basic opens; CommRing.Pic.mk_tensor concerns the Picard group of ring modules. None supplies the Segre pullback of module sheaves. The empty grep and Loogle results agree. The actual log is retained and the new records are copied from it without invented queries.

## Not duplicates

No new nodes were created. In particular, the relative-Proj quotient geometry, homogeneous-fraction construction, and tensor-generation lemmas are cited in their existing nodes rather than duplicated.

## Review by O3

I checked delivery-errors B through E against the four steps with their cited statements open. All proof steps are shorter than 2000 characters, and no step is marked elementary to hide a geometric theorem. There is no statement dispute: arbitrary schemes, including nonreduced or non-Noetherian bases, are allowed throughout.

Step 1 uses lem-trf-symmetric-proj-tautological-chart-gluing for precisely its free-module clause, including the identification of the basis quotient sections with T_i and the affine-local degree-one twist. It uses lem-trf-projective-bundle-quotient-geometry for the quotient-pair bijection under arbitrary S-morphisms, applied to p_1,p_2, so the pulled coordinate families really generate. It uses clause (1) of lem-weil-pbc-invertible-pullback-tensor for invertibility of the tensor product. No quasi-projectivity, flatness, Noetherianity, or finite-type assumption on S is needed: the free modules used here are quasi-coherent and the projective-bundle theorem allows every quasi-coherent module.

Step 2 uses lem-sc-tensor-generating-sections with exactly two factors and finite families of sizes m+1,n+1. Its statement gives the individual pure tensors as generators, rather than merely some unspecified generating family. def-weil-pbc-generating-sections defines this by the surjectivity of the corresponding free-module map, and supplies precisely q. The identification of the pulled free module with the free module on the same basis is the coefficient extension O_P tensor h^{-1}(-) defining pullback.

Step 3 uses the statement of lem-trf-line-quotient-homogeneous-fraction-map, including its explicit ratio formulas, uniqueness, and compatibility with affine base restriction. On product frames the coefficients are a_k c_l, so division by a_i c_j on its invertible locus yields (a_k/a_i)(c_l/c_j). Those are the defining multihomogeneous coordinates of def-chow-segre. This comparison identifies the actual morphism, not just its point map, because the cited theorem characterizes it by all the affine homogeneous-fraction ring maps. This supplies the comparison the rejected attachment lacked while staying entirely in the relative-Proj interface.

Step 4 uses the quotient-compatible isomorphism and the explicit free-module/twist identification in lem-trf-projective-bundle-quotient-geometry. These are in its statement, not merely in its proof. Substitution of F=Segre now gives the required isomorphism on P. No separate unproved gluing or base-change identification is invoked.

I checked S empty (all quotient and chart assertions restrict to the empty scheme), m=0 and n=0 (one coordinate family of size one; the same product construction still applies), and S=Spec(A) for arbitrary A (the theorem uses Proj A[T] and its actual degree-one twist). In particular S=Spec(Z/4) satisfies every hypothesis; the ratio argument does not require reducedness or that a nonzero element is invertible. Inverting the product a_i c_j makes each factor invertible, exactly where the displayed division is used. The two generic off-unit module tools are declared in split_report.tool_uses; no alternate unit route is proposed. Every citation has a verbatim quote in citations.json.

## Unfinished work

None for this one-level stage-1 split. No Lean was written or compiled, and the shared repository was not modified.
