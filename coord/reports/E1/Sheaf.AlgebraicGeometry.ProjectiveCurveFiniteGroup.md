## What changed

The target theorem now applies `finite_group_devissage_of_prime_module_case` and supplies its
prime-order abelian cases using `finite_group_prime_abelian_case`.
The new module `Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroupDevissage` states the finite-group
prime-factor devissage as a named intermediate theorem. The old proof-only imports were removed from
the target module; its public statement imports remain unchanged.

## Proved and sorry left

The target declaration
`AlgebraicGeometry.isConstructibleAbelianSheaf_higherDirectImage_constant_of_projective_curve`
is proved by application of the devissage theorem. Two new sorries remain: `AlgebraicGeometry.finite_group_devissage_of_prime_module_case`, in node
`lem-fin-projective-curve-finite-group-devissage`, for the finite-group induction; and
`AlgebraicGeometry.finite_group_prime_abelian_case`, in node
`lem-fin-projective-curve-finite-group-prime-cases`, for the prime coefficient case and coefficient
forgetting.

## No longer needed

The target no longer imports or directly uses these proof-only modules from its former route:
`Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`,
`Mathlib.CategoryTheory.Sites.Sheafification`,
`Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor`,
`Sheaf.Paper.SheavesKilledByNZmodModules`,
`WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`,
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`,
`WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`,
`Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`,
`Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`,
`Sheaf.CategoryTheory.RingedSiteModules`,
`WeilConjectures.ConstructibleSheaf.KernelCokernel`,
`WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor`,
`WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`,
`Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison`,
`WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`,
`Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`, and
`Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`.
Their proof dependencies are now carried by the two new intermediate modules and their stated nodes.

## Where the brief, the DAG or earlier work was wrong

The original seven-step proof plan is substantially larger than the declarations available to this
module. The finite-group induction and all categorical exactness work are therefore recorded as a
strictly stronger intermediate theorem with the prime-order module cases as an explicit premise.

## New nodes

`lem-fin-projective-curve-finite-group-devissage` records the finite-group prime-factor induction
used by the target. `lem-fin-projective-curve-finite-group-prime-cases` records the prime-order
abelian coefficient input. Their Lean declarations are in
`lean/Sheaf/AlgebraicGeometry/ProjectiveCurveFiniteGroupDevissage.lean` and
`lean/Sheaf/AlgebraicGeometry/ProjectiveCurveFiniteGroupPrimeCases.lean`.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
