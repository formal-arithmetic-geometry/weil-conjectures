## What changed

Proved `AlgebraicGeometry.Etale.smooth_localAcyclicity` using the existing smooth
base-change theorem, strict-local exchange criterion, strict-base closed-point
localization comparison, and canonical constant-coefficient comparison. The public
statement and both public imports are unchanged. All new helpers are private and proved.
No source-library files or consumers are changed.

The argument follows Stacks 0GJQ by replacing the base by its strict localization.
The evaluation into the geometric field is local, so the admissible integer becomes
invertible there. Smooth base change gives bijective cohomology pullbacks from a
separably closed field to the strict-local fibre. In degree zero the proof identifies
the actual constant-section unit, rather than just constructing an unrelated group
isomorphism. The existing strict-local constant comparison identifies the actual alpha.

## Proved and sorry left

Closed the single original hole: `AlgebraicGeometry.Etale.smooth_localAcyclicity`.
One of one original sorries proved; zero holes added or split off; no sorry remains
in this module. Existing dependency theorems are used with their declared statements.

## No longer needed

The affine-open/initial-subcategory refinement and separate geometric-fibre test are
unnecessary: the existing strict-base closed-point localization theorem compares every
test fibre directly. The finite-constant derived-cohomology wrapper is also unnecessary:
the proof uses strictly henselian acyclicity and the canonical sheafification unit.
The local constant comparison supplies the alpha calculation. These are changes to this
item's route; no other module is withdrawn and no claim of global unreachability is made.

Removed the unused trial import
`WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections` as well.

The trial import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapDevissage` was also
removed: its coefficient-isomorphism step follows directly from cohomology naturality
and functorial preservation of isomorphisms, without the larger devissage development.

Removed original private imports:

- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.CategoryTheory.Filtered.Final`
- `Mathlib.CategoryTheory.Limits.Final`
- `Mathlib.CategoryTheory.Limits.HasLimits`
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Sheaf.AlgebraicGeometry.StrictLocalGeometricFibreTest`
- `Sheaf.AlgebraicGeometry.StrictlyHenselianConstantCohomology`
- `Sheaf.Paper.StrictHenselizationFunctoriality`
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`
- `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization`
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension`
- `WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

Removed direct proof dependencies:

- `def-weil-pbc-strict-henselization-limit`
- `lem-weil-pbc-colimit-initial-full-subcategory`
- `lem-weil-pbc-inverse-image-stalk-germ`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-weil-pbc-strict-local-geometric-fibre-test`
- `lem-weil-pbc-strictly-henselian-sections-stalk`
- `sbc-lem-strict-henselian-constant-cohomology`

Some ingredients, including strict-local germ compatibility, remain transitive dependencies
of the imported comparison theorems; removal here does not remove those declarations.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or interface repair was needed. The planned geometric-fibre test
and affine-open reduction were longer than the existing strict-base comparison route.
Updated the node's proof, proof dependencies and proof origin to describe the argument
actually formalized. No new DAG nodes were introduced.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
