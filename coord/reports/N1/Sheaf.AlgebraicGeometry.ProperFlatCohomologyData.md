## What changed

Repaired `ProperFlatCohomologyData.lean` for the returned duplicate-theorem finding.
Removed its private `AlgebraicGeometry.Scheme.Modules.flatOver_morphismRestrict`.
Added the proof-only import `Sheaf.AlgebraicGeometry.FlatOverAffineOpenRestriction`
and applied its public `AlgebraicGeometry.isFlatOver_affineOpenRestriction` to the
chosen affine neighbourhood. The existing duplicate itself is private, so it cannot
be applied across modules. The proof transports the public result along the inverse
of `overFunctorEquiv` and the inverse spectrum-chart isomorphism, using evaluated
module isomorphisms, ring-isomorphism flatness and transitivity. Added proof-only
Mathlib flatness imports for this transport. The target statement is unchanged.
Updated the target node's first proof step and dependency list to record this reuse.
The four supporting modules and their nodes are retained from the returned delivery.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_proper_flat_cohomology_model_data`
(node `lem-pc-proper-flat-cohomology-model-data`) by decomposition through an explicit
finite affine Cech complex. The supporting theorem
`AlgebraicGeometry.Scheme.Modules.finiteAffineCechModel_flatOver` is proved.
The item's module has no remaining `sorry`.

Two split-off holes from the original delivery remain:

- `AlgebraicGeometry.Scheme.Modules.flatOver_affineAssociatedModule`, node
  `lem-pc-affine-associated-module-flat-over`, module `AffineAssociatedModuleFlatOver`.
- `AlgebraicGeometry.Scheme.Modules.finiteAffineCechModel_comparison`, node
  `lem-pc-finite-affine-cech-model-comparison`, module `FiniteAffineCechModelComparison`.

This is a decomposition of one upper hole into two lower holes, not a claim of a
sorry-free transitive proof. The present repair adds no holes.

## No longer needed

Removed the duplicate private `flatOver_morphismRestrict` declaration; its direct
open-image calculation is replaced by the existing public affine-restriction theorem.
The original item's proof-only imports `Sheaf.AlgebraicGeometry.AlternatingCechComputes`,
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray` are removed from the item.
The finite-model comparison now contains the comparison obligation, so the item has
no direct use of these former dependencies. No supporting node is pruned by this repair.
Earlier rejected private helpers `flatOver_postcomp_iso`, `flat_affine_sections` and
`flat_alternating_sections` remain absent from `FiniteAffineCechModelFlatOver`.

## Where the brief, the DAG or earlier work was wrong

The returned delivery repeated a private theorem already present word for word in
`FlatOverAffineOpenRestriction`. The existing declaration is inaccessible externally;
its module's public affine-chart restriction theorem supplies the needed mathematical
fact. The repair imports and uses that public theorem instead of repeating the private
one. The target node now records the actual dependency and the explicit inverse-chart
transport. No statement, definition, visibility or existing public interface changed.

## New nodes

The original delivery's four new supporting nodes remain:
`def-pc-finite-affine-cech-model` constructs the actual finite complex and proves its
bounds and quasi-coherence; `lem-pc-affine-associated-module-flat-over` isolates the
affine associated-module flatness assertion; `lem-pc-finite-affine-cech-model-flat-over`
proves termwise flatness from that assertion; and
`lem-pc-finite-affine-cech-model-comparison` isolates universal cohomology comparison.
Their statements, source citations and searches are unchanged. This repair creates
no additional nodes and requires no interface change record.

## Second reading by N1

1. **Visible changes and signatures.** I diffed the delivered item against the repository version. The existing target declaration and its docstring are unchanged; the repair only changes proof imports, proof code, and the DAG proof route. The four additional modules are new supporting modules, and their declarations match the corresponding node `lean.statement` fields byte for byte. No unrelated repository module was edited.

2. **Compilation and proof status.** I compiled all five sandbox modules with `lcompile.py --all`; they compile without errors. The target module has no `sorry`. The only remaining `sorry`s are the two named split theorems `flatOver_affineAssociatedModule` and `finiteAffineCechModel_comparison`, exactly as listed above and represented by their nodes. Axiom checks show only the permitted base axioms plus `sorryAx` where those split theorems are in the dependency closure.

3. **Statements and split nodes.** I checked each supporting statement against its node and source description. The explicit finite Cech model is a real construction with boundedness and quasi-coherence properties; the affine-associated-module theorem and the universal comparison theorem are strictly lower, separately named obligations rather than restatements of the target. Their hypotheses and conclusions are unchanged from the delivered nodes, and no definition contains `sorry`.

4. **Shortest route and pruning.** The target proof uses the public `isFlatOver_affineOpenRestriction` theorem and transports it through the inverse affine chart and the evaluated module isomorphism, removing the duplicate private helper. The comparison, explicit-model, and flatness modules are all used by the final proof. The former direct Cech/Leray imports are absent and recorded under `## No longer needed`; no retained node is unused.

5. **Unit route and DAG agreement.** The target and all four supporting nodes remain in `sk-thm-picard-coherence`, and the target node's proof steps, dependencies, and origin describe the actual Lean route. The finite model, termwise flatness, and comparison are used in that order, while the public affine-open flatness node supplies the restriction step. The unit's realized route is therefore preserved.

I changed only this report section after the initial review; no Lean source, node statement, or definition was altered during second reading.
