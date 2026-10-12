## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.nonempty_etale_openCech_resolution_total_iso`
by a compiling proof. The original statement and public imports are unchanged.
Private helpers construct the degree-zero restriction map, prove its naturality,
and prove that its first Čech differential vanishes. The proof explicitly constructs
the chain map from the evaluated resolution into the total complex, checks the total
signs, applies `HomologicalComplex₂.quasiIso_of_column_augmentation`, and composes
with Mathlib's `InjectiveResolution.isoRightDerivedObj`.

Added proof imports of `Sheaf.Algebra.Homology.FirstQuadrantAugmentation` and
`Sheaf.AlgebraicGeometry.EtaleOpenCechInjectiveAugmentation`. The latter isolates
only the single-injective-sheaf row comparison (original steps 1 and 2), with no
resolution, total complex, or derived functor. Every object and map in the target
proof is concretely constructed; no data is chosen from an unproved existence claim.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.nonempty_etale_openCech_resolution_total_iso`
(node `lem-sc-etale-open-cech-resolution-total`).

Added one hole:
`AlgebraicGeometry.Scheme.etaleOpenCechInjectiveAugmentation_quasiIso`
(node `lem-sc-etale-open-cech-injective-augmentation`). This is a decomposition:
one upper hole closed, one strictly simpler row-comparison hole added, net zero
holes. The target module has no remaining direct `sorry`. Its proof still depends
on the new row theorem and the existing first-quadrant theorem and their dependencies.

Both delivered modules compile together without errors or warnings through
`lcompile.py --all`. Edge cases checked mathematically: an empty cover forces the
section object to be zero by the sheaf condition; a singleton covering reduces to
the usual restriction augmentation; degree zero uses sheaf gluing and positive
degrees use injectivity. No boundedness of the injective resolution is introduced.
The first-quadrant theorem supplies convergence along finite diagonals.

## No longer needed

No original imports removed; no node or module is pruned. The original positive
injective Čech acyclicity dependency is moved into the new single-row item's plan,
so it remains needed transitively. Its absence from the target's direct proof_deps
is not pruning. All original public imports remain required by the target interface.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the target or its plan was found. The target's starting
module did not yet import its planned first-quadrant criterion. The existing generic
injective Čech augmentation theorem is for categorical products in an over-category
and matches coefficient universe to the Hom universe; it does not directly apply
to this open-pullback complex with coefficients in universe u+1. The remaining lemma
records precisely the product/reindexing comparison and injective row calculation,
rather than duplicating totalization or the target under a different name.

Searches used LeanFinder, Loogle, msearch grep, and local rg on both library roots
and Mathlib. LeanSearch returned Internal Server Error; the unavailability is recorded.
The existing total-section theorem has the same over-category/universe mismatch.
Sources checked: [Stacks 03AW](https://stacks.math.columbia.edu/tag/03AW) and
[Stacks 03F6](https://stacks.math.columbia.edu/tag/03F6).

## New nodes

`lem-sc-etale-open-cech-injective-augmentation`, in
`dag/nodes/sec-curve-estimates/lem-sc-etale-open-cech-injective-augmentation.json`,
is the row augmentation for a single injective étale sheaf on the image of an open
cover. Its theorem is in `Sheaf.AlgebraicGeometry.EtaleOpenCechInjectiveAugmentation`.
The source and complete proof in words appear in both the node and theorem docstring.
The target node's proof, proof_deps and proof_origin are updated to match the Lean.
No existing signature or public visibility changes; no forced adaptations or
change records are needed. The unit record realizes no steps by this node; the
original row-augmentation and first-quadrant route is retained.

## Second reading by G1

1. Compared both delivered Lean modules with the repository versions. Existing declaration signatures and public interfaces are unchanged; the added module is the explicitly recorded split-off statement.

2. Compiled both modules with `lcompile.py --all`; compilation is clean. The only remaining `sorry` is the named split theorem `etaleOpenCechInjectiveAugmentation_quasiIso`, and it has a matching node and proof docstring. No forbidden declarations or hollow definitions occur.

3. Checked the split-off row statement against the source and edge cases. It is a strictly simpler injective single-row augmentation theorem, with no resolution or totalization hypotheses, and the stated empty-cover behavior is consistent with the sheaf condition. It does not duplicate the target theorem.

4. Checked the proof route and imports. The target uses the first-quadrant column criterion and the row theorem; no shorter available library theorem covers the open-pullback and universe combination. The target's original imports remain needed by its interface or proof, and no node is pruned.

5. Checked DAG agreement: theorem names, statements, proof dependencies, proof origins, and the unit route match the delivered Lean. The unit's realized route remains unchanged.

Changed only the report by adding this second-reading record; no Lean proof or statement changes were needed during review.
