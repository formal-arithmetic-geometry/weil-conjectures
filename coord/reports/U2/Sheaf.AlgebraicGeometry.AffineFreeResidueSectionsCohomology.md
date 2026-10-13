## What changed

Replaced the original hole in
`AlgebraicGeometry.Scheme.affineFree_residueSections_cohomologyLinearEquiv`
with a proof establishing section-complex K-flatness, using a comparison of derived
objects, exact sections over the residue field, and the tilde–global-sections unit. The existing signature and public imports
are unchanged. The proof-only imports provide the new derived model, tilde sections over a field,
finite free section coordinates, flat modules, exact filtered colimits, and tensor
colimit preservation. The new module publicly imports the upstream K-flat interface
because its signature explicitly assumes K-flatness of the section complex.

The target proves the section-complex K-flat hypothesis: evaluate the support bound,
identify each section module with finite free coordinates, turn its upper bound into
`IsStrictlyLE`, and apply the proved upstream bounded-above flat K-flat theorem.
The new module states the affine object-level comparison, with that K-flat hypothesis,
before taking homology. The target proof applies `DerivedCategory.homologyFunctorFactors`, commutes homology with
`moduleSpecΓFunctor`, maps `tilde.toTildeΓNatIso` to complexes, and composes the
resulting isomorphisms. It does not construct an arbitrary object from an unproved
existence theorem: the residue section complex and its associated sheaf are explicit.
The unproved comparison supplies only an isomorphism between those fixed objects.

Both DAG records follow this reduction. No existing definition or statement changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.affineFree_residueSections_cohomologyLinearEquiv`
(node `lem-sc-affine-free-residue-sections-cohomology`).

Added one hole:
`AlgebraicGeometry.Scheme.affineFree_residueSections_derivedModel`
(node `lem-sc-affine-free-residue-sections-derived-model`). Its proof is exactly
`by sorry` in its own new module. It states the derived-object comparison and does
not state the target's cohomology equivalence.

This is a decomposition: one original hole closed, one hole added, net zero.
The original module is proved from that comparison, not an axiom-free proof of the
entire mathematical result. The bounded-free-to-K-flat step and the exact sections and homology portion
are now proved.
Both delivered modules compile with no warnings.

## No longer needed

No baseline import is removed. No planned geometric dependency is globally pruned:
`lem-pc-affine-localized-site-derived-transport`,
`lem-pc-affine-kflat-pullback-chart-comparison`, and
`lem-pc-ringed-spaces-derived-pullback-composition` remain in the proof plan of the
new object-comparison node. The bounded-flat K-flat node is used directly in the
original module via the closed generic upstream K-flat theorem. The geometric
comparison modules need not be imported into the original module.

Trial proof-only imports of `Sheaf.Topology.PointModuleEvaluationEquivalence` and
`Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact` were removed. The proved
`isEquivalence_moduleSpecΓFunctor` supplies exactness directly. No existing nodes
or modules become unnecessary through this delivery.

## Where the brief, the DAG or earlier work was wrong

The original plan names the affine localized-site derived transport but does not
provide the section-counit glue as a direct interface. The new object-comparison
node records that remaining glue and retains the planned geometric route. The
existing `AffineProjectiveSectionsSheafification` statement can supply the affine
section presentation after transport through the over equivalence.

The first dry run required the second-reading section despite the worker brief
reserving it for the independent reader. The latest dry run prints OK and explicitly
exempts that section until the second reader writes it. No independent reading
has been written by this worker, and nothing has been pushed.

The unit `sk-prop-av-cube` has no realized nodes for this internal calculation;
its statement and route are unchanged. Edge cases checked: zero ranks, the zero
complex, inverted support bounds, and arbitrary integer cohomological degrees.
An empty U cannot contain the supplied point; no nonempty-rank assumption or
finite-dimensional-cohomology assumption is added.

Searches were run through msearch (LeanSearch, LeanFinder, Loogle, grep), plus repository
signature searches. LeanSearch returned HTTP Internal Server Error and is recorded
as unavailable. The relevant Mathlib declarations for the homology portion
were read in Additive.lean and Modules/Tilde.lean. The Stacks source was read online:
[064K](https://stacks.math.columbia.edu/tag/064K),
[06YI](https://stacks.math.columbia.edu/tag/06YI),
[0098](https://stacks.math.columbia.edu/tag/0098), and
[08DW](https://stacks.math.columbia.edu/tag/08DW).

## New nodes

`lem-sc-affine-free-residue-sections-derived-model`, in
`dag/nodes/sec-abelian-varieties/lem-sc-affine-free-residue-sections-derived-model.json`,
states the comparison of the derived pullback with the explicitly constructed
associated-sheaf residue section complex. Its module is
`lean/Sheaf/AlgebraicGeometry/AffineFreeResidueSectionsDerivedModel.lean`.
The node realizes the affine object-level portion of the original proof, with
K-flatness as an explicit hypothesis. The original module proves that hypothesis
and the homology and exact-section portion. No change record
is needed because no existing signature, definition, or visibility changed.

## Second reading by U2

1. Compared both delivered modules with the repository versions. Existing theorem signatures and definitions are unchanged; the added derived-model theorem is a separate split node with matching declaration and DAG record. Verdict: pass.
2. Compiled both modules with `lcompile.py --all`. There are no errors, warnings, forbidden declarations, or unlisted sorries; the sole sorry is the named derived-model split theorem. Verdict: pass.
3. Read the proof from the target downward. The section-complex K-flat argument uses finite-free coordinates and the bounded-above flat K-flat theorem; the remaining comparison is isolated in a strictly lower object-level statement. The split statement is true by the cited affine and derived pullback route and is exactly as strong as required. Verdict: pass.
4. Checked pruning and imports. Proof-only imports are private, removed trial imports are recorded above, and no old proof dependency is silently dropped. The unit route remains represented by the existing geometric dependencies and the new comparison node. Verdict: pass.
5. Checked node metadata and report consistency. The Lean declaration, statement, proof dependencies, source, and split status agree with the DAG records; edge cases (zero rank and zero complex) introduce no extra hypotheses. Verdict: pass.

Changed only this report by adding the required independent second-reading record; no Lean code or DAG content required repair.
