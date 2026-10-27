## What changed

Prove `AlgebraicGeometry.Etale.exceptionalConstantTensor` from the existing four support
interfaces: unbounded compact-support amplitude, coherent support projection,
compact-image/adjoint coproducts, and coefficient-action adjoint generation.
The theorem signature and the coefficient-tensor and constant-pullback definitions are unchanged.
The public projection map now specializes the real generic constructor
`exceptionalProjectionConstruction`, which is exactly its original composite. The shared
constructor avoids comparing two expanded concrete tensor calculations in the kernel;
see `coord/changes/M8-exceptional-projection-construction.md`. Private helpers, all proved, package
the restriction and reindexing of a projection bifunctor, its unit equation, and shift
compatibility of action morphisms. The generation assembly is generic in the coefficient
category, so its canonical tensor shift and unit instances need no concrete definitional
comparison. Derived pullback preserves coproducts by its named derived adjunction. No source-library module is modified.

Choose the uniform bound before quantifying over coefficients or compactifications.
Apply coefficient-action adjoint generation first with the source action
`V ↦ f* V_Y ⊗ K`. The coherent support projection supplies its shift and unit equations.
The compact-image theorem supplies coproduct preservation of the right adjoint.
Tensor and constant-sheaf functors give the other exactness and coproduct instances.
The abstract theorem uses the degree-zero regular module with carrier `ULift.{0} C`,
identified with the module tensor unit by its explicit linear equivalence. Assemble the mate's two naturality equations and
pointwise invertibility into a natural isomorphism.

Finally transport the source action through `exceptionalConstantPullbackIso`.
Tensor symmetry naturality identifies the transported projection with exactly
`exceptionalConstantProjectionMap`; adjunction naturality identifies the transported mate
with the specified transpose. This avoids comparing two constructions of constant pullback.

Validation: the cleaned item and the unchanged direct consumers
`Sheaf.Paper.EtaleQuotientTensorProjection` and
`Sheaf.Paper.EtaleSystemQuotientNormalization` compile together through `lcompile.py --all`.
The complete instrumented item compiled in 41.8 seconds; its main theorem's kernel check
took 1.45 seconds after sharing the projection construction.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.Etale.exceptionalConstantTensor`
(node `lem-pur-etale-exceptional-constant-tensor`), from the existing support interfaces.
There are zero remaining holes in the item and zero new holes or split-off statements.
The retained `ActionMateIso` and `EtaleActionGeneration` drafts are not delivered: the
naturality assembly and restricted-generation argument are complete private proofs here.
This is a proof relative to the imported support declarations, whose proof status is unchanged.

## No longer needed

The following direct proof imports from the old ten-step plan are removed. Their needed
mathematics is supplied through the existing support results; this does not claim that
all these modules leave the targets' transitive import closure.

- `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`
- `Sheaf.AlgebraicGeometry.DimensionExtension`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportAmplitude`
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`
- `Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit`
- `Sheaf.CategoryTheory.FunctorPreservesSequentialHomotopyColimit`
- `WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`
- `Mathlib.Topology.Defs.Filter`
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Sheaf.AlgebraicGeometry.FiniteTypeSheafFiniteness`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `WeilConjectures.CategoryTheory.CompactTestsRightAdjointCoproducts`
- `Sheaf.Paper.ProjectionMateExact`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.CategoryTheory.Triangulated.GeneratingClassDetermination`
- `WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration`
- `Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators`

No declaration or module is withdrawn. The current four-part DAG proof route is retained;
its generating-class and free-generation arguments are supplied by
`coefficientActionAdjointGeneration`. The DAG description records that generation is applied
before transporting the source action. These two dependencies remain in the node, including
the reviewer-retained unit-route citations. No DAG node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original module docstring describes the older ten-step plan; the current node already
packages those steps into four stated support lemmas. The proof body follows that assembly;
the original detailed docstring is retained.
A compactification need not be selected by an existence theorem: the empty family case
is vacuous, and otherwise a witness can be used to obtain the geometric bound. This
choice is confined to a proof, with no new definition or arbitrary data exported.
The coherent support projection and this module use two constructions of constant pullback;
the proof applies generation before transporting the action, without assuming they coincide.

The resumed packet initially had two unfinished helper modules, but listed only one of their
holes in the report. Its private helpers were inaccessible across the module boundary and
its generation call omitted the coefficient-ring argument. This delivery repairs those
issues within the item module and removes the development profiling and transparency options.
The compact-image theorem supplies the right-adjoint shift structure and triangulatedness.
A proved private helper derives unit-shift compatibility from its counit equation using
naturality and both adjunction triangle identities. No second shift structure is constructed.
The amplitude interface carries triangulatedness for its own direct-derived shift structure.
The assembly uses the canonical adjunction-compatible shifts from the source-library
`Triangulated` module and explicitly discards the auxiliary instance with the `-`
destructuring pattern; the amplitude conclusions are unchanged. The final comparison is
inferred before it is matched with the target. The public projection and the proof use the same generic construction, so their equality
does not require reducing the full concrete derived tensor. Controlled unfolding only exposes
the local action and the public wrappers.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
