## What changed

Proved `AlgebraicGeometry.Etale.stalk_faithful_derived` in
`Sheaf.AlgebraicGeometry.StalkFaithfulDerived`, preserving its statement.
The converse applies `DerivedCategory.isIso_iff`, commutes exact inverse image
with homology using `Functor.mapDerivedCategoryHomologyFunctorIso`, and
identifies geometric fibres using `upperStarCompUliftSheafFiberIso`.
Ordinary geometric stalk conservativity proves each homology map invertible.
The forward implication is functorial preservation of isomorphisms.

Updated the node's proof, proof dependencies and proof origin to follow this
route. Added the proof import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
Removed unused private proof imports. All original public imports, declaration
signatures and definitions are unchanged.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Etale.stalk_faithful_derived`
(node `lem-kun-stalk-faithful-derived`). Added 0 holes and split off 0 theorems.
No `sorry` remains in the delivered module.

The current module compiled through `lcompile.py` in 2.3 seconds, with exit
code 0 and no diagnostics. The required delivery dry run also compiled it
and passed preflight, with review class CODEX because the node file changes.

## No longer needed

Removed private imports:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`
- `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`
- `Sheaf.AlgebraicGeometry.GeometricStalkCohomology`
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`
- `Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`
- `Sheaf.AlgebraicGeometry.DerivedGlobalGerm`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`

Removed proof dependencies `def-weil-triangulated-category`,
`lem-kun-distinguished-cone-zero`, `def-weil-abstract-derived-category`,
`lem-kun-stalk-as-pullback`, `lem-kun-stalks-of-cohomology`,
`lem-weil-pbc-geometric-point-pullback-stalk`,
`prop-weil-pbc-geometric-stalks-exact`, and `lem-kun-d-zero-cohomology`.
The proof handles homology maps directly, so does not form cones, test zero
objects, construct derived global sections, or choose objectwise stalk
comparison isomorphisms. The natural underived fibre comparison is used from
`lemma-openclosed-stalk-upperstar`; its module stays imported. Removed the
obsolete top-level tool approval
`lem-weil-pbc-geometric-point-pullback-stalk`.

These dependencies are pruned from this proof; other consumers may still
need them. The unit record has no realized steps, so this route preserves
every fixed unit realization. Exactness and the derived-category structures
remain available through the retained imports.

## Where the brief, the DAG or earlier work was wrong

The original cone route is valid but longer than the available homology-map
criterion. The objectwise `Nonempty` comparison in
`nonempty_geometricStalk_cohomology_iso` alone supplies no naturality in a
morphism; the proved natural comparison supplies the API used here.
No mathematical statement correction was necessary. Empty schemes cause no
extra assumption: ordinary stalk conservativity also covers an empty family
of canonical geometric points.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
