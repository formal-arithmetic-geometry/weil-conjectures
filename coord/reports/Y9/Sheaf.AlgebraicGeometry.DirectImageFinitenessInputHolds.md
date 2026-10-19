## What changed

Replaced the single sorry in
`AlgebraicGeometry.Scheme.hasDirectImageFinitenessInput_of_isSepClosed`
with a complete Lean proof of the unchanged statement. No definitions or public imports changed.

The proof follows both original DAG steps. For clause (1), invertibility excludes N = 0;
its positive natural absolute value is an invertible annihilator, including negative N.
Map its unit into global sections of Spec k. A constructible sheaf placed in degree zero
is bounded constructible: degree zero is identified by the single/homology isomorphism,
and all other cohomology is zero. Apply
`isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field`
and extract constructibility in degree q.

For clause (2), install the supplied structure map as the Over instance. On the empty
scheme every sheaf is zero, so its single complex, derived global sections and homology
are zero. Otherwise the irreducible closed closure of a point excludes dimension bottom.
The dimension upper bound excludes infinity, giving an exact natural dimension e <= d.
Apply the separably closed field bound and the finite-type torsion cohomological-dimension
theorem with c = 0 and dimension e, and use 2*e <= 2*d.

Added proof-only imports
`Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison` for the constructibility API,
`WeilConjectures.CategoryTheory.DerivedCategory.Constructible` for the degree-zero lemma,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive` and
`WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections` for preservation of zero
by derived global sections. Edge cases covered by the proof include the zero coefficient
ring, negative annihilators, empty schemes, and dimension zero. No nonemptiness,
separatedness, or uniform annihilator hypothesis was added.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.hasDirectImageFinitenessInput_of_isSepClosed`
(node `thm-exc-direct-image-input-holds`). No sorry remains in the delivered module.
No holes added and no intermediate statements split off. This is a proof from the existing
declared dependencies, not a decomposition.

On resumption, checked the retained proof against the current predicate, dependency
signatures and DAG steps. The required deliver3.py dry run compiled the module and
passed preflight with review class AUTO.

## No longer needed

Removed these redundant direct imports, whose required declarations remain available
through the retained public dependency interfaces:

- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`
- `Sheaf.AlgebraicGeometry.DerivedCategories`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`

All five original proof-dependency nodes remain used: finite-type constructibility,
bounded constructible complexes, the separably closed torsion dimension bound,
the finite-type torsion dimension bound, and its defining predicate. No mathematical
DAG branch is bypassed and no module is claimed to leave the targets' transitive closure.
The original DAG proof and proof_deps still describe this proof; no node file changes.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect was found. The original plan's explicit empty/nonempty split
and signed-annihilator conversion are both necessary for these interfaces and are now
implemented. Server compile attempts sometimes returned no response after the retry window;
those were retried using the prescribed lcompile.py tool.

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
