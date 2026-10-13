## What changed

Proved `AlgebraicGeometry.Scheme.Modules.cechInverseImage_degree_zero` with its original
signature and visibility. Three fully proved private helpers establish augmentation
naturality, transposition of the constant-sheaf comparison, and the action of exact
inverse image on Ext-zero sections. The final proof represents the Cech input by its
unique global section and compares these two explicit calculations.

Replaced the public import of `CechComparisonSystem` by `FlatCohomologyComparison`,
which supplies the inverse-image and constant-sheaf objects used by the statement.
Updated the existing DAG node's proof, proof dependencies and proof origin to match.
Import change record: `coord/changes/cechInverseImageDegreeZero-import-pruning.md`.
No new modules, nodes, definitions, statements, axioms or forced adaptations.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.cechInverseImage_degree_zero`
(node `lem-pc-cech-inverse-image-degree-zero`).

Holes added: none. Sorries left in the item or added elsewhere: none.
This is a complete proof, not a decomposition. The three private helpers are proved.
The file compiles without errors or warnings in approximately four seconds.
`#print axioms` of the public theorem reports exactly `propext`, `Classical.choice`,
and `Quot.sound`; it does not depend on `sorryAx`.

The argument assumes neither an inhabited cover index nor a nonempty scheme; the
existing Cech zero isomorphism handles empty covers. No new statement needs a separate
edge-case check. The theorem signature was retained verbatim.

## No longer needed

Removed direct import `Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystem`, and
removed node `def-pc-cech-comparison-system` from this node's proof dependencies.
The statement-dependency metadata is unchanged. The unit record has empty realized
statement/step lists; no unit-level route is bypassed.

The repository import graph loses the following project modules from this item's
closure. This is local pruning; the sole direct importer already imports
`CechComparisonSystem`, so no claim is made that these leave the targets' closure:

- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullback`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackComparison`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackRepresentatives`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback`
- `Sheaf.Algebra.Homology.OpenCoverAdjunctionTriangle`
- `Sheaf.Algebra.Homology.OpenCoverMateComplexShortExact`
- `Sheaf.Algebra.Homology.OpenCoverMateModuleShortExact`
- `Sheaf.Algebra.Homology.OpenCoverMateModuleShortExactCore`
- `Sheaf.Algebra.Homology.OpenDerivedMatePresentation`
- `Sheaf.Algebra.Homology.OpenHomTriangleRealization`
- `Sheaf.AlgebraicGeometry.Coherent`
- `Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystem`
- `Sheaf.AlgebraicGeometry.Cohomology.FlatAffineSectionRingTensor`
- `Sheaf.AlgebraicGeometry.Cohomology.FlatAffineTensorReassociation`
- `Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyAffineSections`
- `Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyCechBaseChange`
- `Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyCechDifferential`
- `Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyCechTerms`
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineChartUnit`
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSectionsBijective`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`
- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`
- `Sheaf.CategoryTheory.PresheafChangeOfRingsAdjunction`
- `Sheaf.CategoryTheory.SiteExtensionByZeroExact`
- `Sheaf.CategoryTheory.SiteExtensionByZeroPresheaf`
- `Sheaf.CategoryTheory.SiteExtensionByZeroPresheafAdjoint`
- `Sheaf.Paper.DerivedHomMayerVietoris`
- `Sheaf.Paper.SiteRestrictionExact`
- `Sheaf.Topology.InverseImageModule`
- `Sheaf.Topology.InverseImageOperationExt`
- `Sheaf.Topology.InverseImagePresheafModule`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`
- `WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine`
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde`
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.FromJoel.Algebra.Homology.Double`
- `WeilConjectures.FromJoel.Algebra.Homology.DoubleHomology`
- `WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso`
- `WeilConjectures.FromJoel.CategoryTheory.Limits.ExactFunctor`
- `WeilConjectures.FromJoel.CategoryTheory.Localization.LocalizerMorphism`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Projective`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `WeilConjectures.Mathlib.Algebra.Homology.ExactSequence`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors`
- `WeilConjectures.Mathlib.Algebra.Homology.SingleHomology`
- `WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.Basic`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Kernels`
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`
- `WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafHom`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.SpectralObject`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject`
- `WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic`
- `WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus`
- `WeilConjectures.Mathlib.Topology.Sheaves.Presheaf`
- `WeilConjectures.Topology.Sheaves.CechComparison`

All retained direct imports supply definitions that occur in the original statement.
The import-cycle check and source import-pruning check pass.

## Where the brief, the DAG or earlier work was wrong

The degree-zero node already had a sound direct proof plan. Its import and proof-dependency
list unnecessarily included the comparison-system node, despite its own docstring stating
that no comparison system is involved. The proof needs only the zero augmentation and
the constant-sheaf adjunction. No mathematical statement was changed or disputed.

The locally mirrored literature directory contains only indexes, so the cited Stacks
Tags 01FD and 01EQ were read from their official pages. No missing literature is needed
for an unfinished theorem: this delivery leaves none.


## Second reading by V4

1. PASS: Compared the delivered module with the repository using `diff` and
   separately compared the complete existing theorem signature byte for byte.
   Its signature, visibility, docstring and all existing definitions are unchanged.
   The only public interface change is the documented import substitution in
   `coord/changes/cechInverseImageDegreeZero-import-pruning.md`.
2. PASS: Independently compiled the delivered file with `lcompile.py`: no errors
   or warnings. A scratch copy printed axioms for all three private helpers and
   `AlgebraicGeometry.Scheme.Modules.cechInverseImage_degree_zero`; each uses only
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   The delivered source contains no `sorry` or forbidden declaration mechanism.
   No definitions or arbitrary witnesses from unproved existence are introduced.
3. PASS: No statements were split off and no holes were added. Read all three
   proved helpers: augmentation naturality follows tuplewise from coefficient
   naturality and restriction composition; the constant comparison uses the
   actual uniqueness-of-left-adjoints definition; Ext zero reduces to ordinary
   morphisms and evaluation on the integer generator. None assumes nonemptiness.
   Empty schemes and empty cover indices are covered by the existing zero
   isomorphisms. No lower statement merely restates the item.
4. PASS: Searched the repository with augmentation, constant-adjunct and Ext-zero
   terminology and independently ran LeanFinder for pullback on zeroth sheaf
   cohomology and the adjunction unit. No shorter matching theorem was found.
   `ConstantSectionAdjunctPullback` concerns the small etale site and a different
   coefficient universe, so cannot replace the Zariski helper here. The proof
   already uses the existing Cech zero isomorphism and Ext zero identities.
   Both retained public imports supply objects occurring in the signature.
   `## No longer needed` lists the sole removed old proof dependency and direct
   import; it correctly limits the longer module list to local closure pruning.
   The unit `sk-thm-picard-rr` has empty realized statement and step lists; the
   change does not replace any realized unit step. Compiled the unchanged sole
   direct importer `CechComparisonInverseImageUnit` against a scratch overlay of
   the revised module: no errors or warnings. It directly publicly imports the
   removed dependency itself, so no forced adaptation is needed.
5. PASS: Compared the node records. Only `proof`, `proof_deps`, and `proof_origin`
   differ; the statement and its Lean record are unchanged. The proof steps
   describe the actual three helpers and the final cancellation argument.
   `proof_deps` is exactly the union of the steps' `uses`, and excludes the unused
   comparison-system node. There are no new nodes to audit.

Second-reading changes: appended this review and its independent verification
results to the report. No Lean, DAG, or change-record repair was necessary.
