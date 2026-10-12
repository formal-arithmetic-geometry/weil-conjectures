## What changed

Completed the representative and cokernel algebra in
`Sheaf.AlgebraicGeometry.EtaleComplexFiltrationPageData`, using the existing sandbox
reductions `EtaleComplexUniformPages` and `EtalePresentationImageFiltration`.
Representatives are chosen directly from filtration membership, with their images
fixed by the monic step inclusions. The private `step_quotient_zero_iff` and
`cokernel_map_apply` helpers are proved from Mathlib exactness and `cokernel.π_desc`.
All proof imports are private. The second reading restored private imports of
EtaleHypercohomologyPullbackFunctorial, BoundedFilteredComplexSpectralSequence, and
HomologicalComplexLimits in the uniform-pages reduction, matching its proof plan. Explicit `le_refl 1` arguments replace default
first-page arithmetic tactics in both page-data and uniform-pages signatures.
These proof annotations preserve their elaborated types by proof irrelevance.
The change record is `coord/changes/etale-complex-page-explicit-bounds.md`.

Validation: `lcompile.py --all` compiled uniform-pages in 12.6 seconds,
image-filtration in 2.7 seconds, and page-data in 47.1 seconds with no warnings.
A separate scratch compatibility theorem used the original unedited signature
and applied the delivered theorem directly; it compiled, confirming that the
explicit first-page proof arguments preserve the original elaborated type.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Etale.exists_etaleComplexFiltrationPageData`.
The two private helpers are proved. No sorry remains in the item's module.
Two lower holes remain in the delivery:

- `AlgebraicGeometry.Etale.exists_etaleComplex_uniform_pages`, node
  `lem-weil-pbc-etale-complex-uniform-pages`.
- `AlgebraicGeometry.Etale.etalePresentation_image_filtration`, node
  `lem-weil-pbc-etale-presentation-image-filtration`.

This is a decomposition: one original hole closed and two lower holes added,
net -1 before pruning. The proof combines the two statements through unique lifts,
transition membership, cokernel naturality, exactness, and monicity at the limit.
It is not a fully closed proof of the target import closure.

## No longer needed

Removed direct proof imports `Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial`,
`Sheaf.CategoryTheory.HypercohomologyFirstPage`, `Sheaf.CategoryTheory.KInjectiveBridge`,
`Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`, and
`Mathlib.Algebra.Homology.HomologicalComplexLimits` from the item's module.
The original direct dependencies `lem-weil-pbc-hypercohomology-e1-pullback-functorial`,
`thm-sp-if-e1`, `thm-sp-spectral-object-yields`, and `def-sp-kinjective-bridge`
are replaced there by the two new reductions. The first three remain proof
requirements of the reductions; KInjectiveBridge remains a presentation dependency.
None of those modules is claimed globally pruned. No other planned node is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier session's complete proof had never passed compilation: in addition to
its timeout, it referenced the nonexistent `cokernel.π_map`. The correct Mathlib
identity is `cokernel.π_desc`, used through a proved elementwise helper.
Implicit first-page bounds repeatedly invoked the default `lia` tactic; explicit
proofs expose the same statements without that cost. Broad simplification and
repeated inverse transport were replaced by direct lifts and named identities.
The two intermediate statements are genuine parts of the original argument and
retain the unit route. No mathematical statement or definition was weakened.

## New nodes

`lem-weil-pbc-etale-complex-uniform-pages` separates functorial page construction,
uniform convergence, and filtered abutment maps. It does not give class representatives,
their kernel criterion, or their transition and limit vanishing properties.

`lem-weil-pbc-etale-presentation-image-filtration` identifies the presentation's
canonical filtration with the image predicate through stupid truncation. For q
below the lower bound the truncation is K; above the cohomological degree both
images vanish. Zero complexes and all integer indices are included.

The source and complete proof in words of each open statement remain in its
module docstring and DAG node. The page-data DAG records their combination.
Change record: `coord/changes/etale-complex-page-explicit-bounds.md`.

## Second reading by E2

1. Compared the delivered page-data module with the repository using `diff -u`.
   The definition `complexTermCohomologyMap` is byte-for-byte unchanged. The only
   existing signature changes are explicit `le_refl 1` proof arguments, declared
   in `coord/changes/etale-complex-page-explicit-bounds.md`. An independently
   reconstructed scratch theorem with the exact original signature applied the
   delivered theorem directly and compiled. Proof irrelevance preserves the
   elaborated type. No target, hypothesis, conclusion, or definition changed.
   The other two modules are new. Verdict: pass.

2. Compiled all three delivered modules through `lcompile.py --all`, without
   warnings or errors (11.2, 2.8, and 43.1 seconds after import repairs). Read
   the exactness helper, cokernel naturality helper, representative construction,
   transition proof, kernel equivalence, and limit-zero proof. Only the two
   reported public theorems have `sorry`; there is no prohibited declaration or
   hollow definition. Representatives chosen inside the theorem are uniquely
   fixed by their monic inclusion; no public definition chooses arbitrary data
   from an unproved existence statement. Scratch `#print axioms` checks and the
   explicit axiom checks validate the permitted axioms, with `sorryAx` confined to
   dependence on open statements. Verdict: pass as a decomposition.

3. Read both new theorem statements, their complete docstring arguments, and
   their node records. The uniform-pages statement omits H, eH and all class
   representatives and kernel criteria; the image-filtration statement omits
   the entire diagram and page construction. They are genuine separate parts,
   combined by the proved representative algebra, not renamed copies of the
   item. Checked zero complexes, q below the support bound, q greater than p,
   negative resolution degrees, and singleton diagrams. In these cases the
   filtration is respectively zero, exhaustive, or zero above p, and the uniform
   support bound still applies. Independently searched with msearch leanfinder
   and loogle, and rg in Mathlib, lean/Sheaf and upstream Lean. Found cokernel.π_desc
   and the stupid-truncation inclusion API; no existing theorem supplies either
   complete reduction. Neither remaining hole is a few-minute closure.
   Verdict: pass, with two lower holes and net -1 before pruning.

4. Checked the shortest-route requirement against the upstream stupid-truncation
   APIs, HypercohomologyFirstPage, and EtaleHypercohomologyPullbackFunctorial.
   They supply ingredients but do not supply a uniform bound for the entire
   diagram or the image-predicate dictionary. The main proof uses Mathlib
   exactness directly. All four old proof dependency nodes and all five removed
   direct imports are accounted for in `No longer needed`; none is claimed
   globally pruned. Read dag/units/sk-prop-h2.json: its realized statement and
   step lists are empty, and this below-unit refinement bypasses no realized
   unit step. Verdict: pass.

5. Checked the main node's two proof steps and proof_deps against the two actual
   theorem applications; checked both new nodes' source, statement dependencies,
   proof plan, proof origin, searches, creation, blueprint, chapter, unit and
   verbatim Lean statement records. Restored missing private imports in the
   uniform-pages module so its stated proof dependencies remain available.
   The image-filtration node's first-page dependency is publicly reached through
   EtaleTermwiseHypercohomology. Verdict: pass.

Changes made by the second reading: restored the uniform-pages proof imports;
removed five redundant public imports from the new image-filtration module;
recorded independent searches in both new nodes; added this review. The proved
representative algebra and all mathematical statements were retained.

Second-reading validation details: the independently reconstructed original-signature
check compiled in 32.5 seconds. A scratch copy of the full page-data module with
six explicit `#print axioms` commands compiled in 52.9 seconds: the definition and
both private helpers use only propext, Classical.choice and Quot.sound; page-data
and both reductions additionally use sorryAx. The deliver3 dry run printed OK and
classified the delivery CODEX. Its broader per-declaration probe on page-data
hit the 60-second timeout; the tool reports that the merge runs this probe again.
The successful explicit checks above do not replace that outstanding broader probe.
