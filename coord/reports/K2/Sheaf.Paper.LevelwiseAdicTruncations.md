## What changed

Proved `AlgebraicGeometry.Scheme.pbc_levelwise_truncation_origins` in
`Sheaf.Paper.LevelwiseAdicTruncations`, with its statement unchanged. Both bounded-below
etale witnesses are constructed from the actual standard truncations of the retained
origins. Their alpha isomorphisms are explicit fully faithful preimages of the specified
fixed-ring truncation comparisons. The alpha equations follow by functoriality and
cancellation, rather than by choosing arbitrary witnesses.

The transition squares follow from the unit law for the canonical tensor/restriction
mate and the input witnessed tower's compatibility equation. The lower square uses
the truncation counit universal property; the upper square uses its dual unit property.
All new helpers are private and proved. No public signature or definition changes.
The command-scope review return is addressed by
`coord/changes/levelwise-adic-truncations-command-scope.md`, which records the
module-local options, opens, variables, and attributes retained by the rebased file.
The module-local `warn.sorry` option was removed because the hole ledger interpreted
the option name itself as an unattributed `sorry`; the compiler-wide option remains
unchanged.
The node's eighth proof step now records this argument and explicitly cites the existing
witness-compatibility node. The other proof steps remain the plan for the remaining holes.

Removed unused private proof imports. The resulting module compiles cleanly through
`lcompile.py` (14.6 seconds in the final validation). The axiom audit of the completed
clause still includes `sorryAx` through existing library dependencies, including the
invertibility theorem for the canonical tensor mate. This is a proof from the existing
stated interface, as required by stage 3, rather than an axiom-complete target proof.

## Proved and sorry left

Closed 1 of the 7 original holes:

- `AlgebraicGeometry.Scheme.pbc_levelwise_truncation_origins`.

Added 0 holes; split off 0 statements. The 6 remaining holes, all attached to
`prop-weil-pbc-levelwise-truncations`, are:

- `AlgebraicGeometry.Scheme.pbc_adic_levelwise_truncations`.
- `AlgebraicGeometry.Scheme.pbc_reduction_adic_tower_laws`.
- `AlgebraicGeometry.Scheme.pbc_levelwise_tor_of_uniformizer_injective`.
- `AlgebraicGeometry.Scheme.pbc_levelwise_truncations_constructible`.
- `AlgebraicGeometry.Scheme.pbc_levelwise_truncation_counterexample`.
- `AlgebraicGeometry.Scheme.pbc_levelwise_truncation_compatible_origins`.

The five previously completed clauses are retained with their proofs unchanged.

## No longer needed

The completed origin clause requires no additional imports beyond the module's public
statement interfaces. Removed these unused private proof imports:

- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`.
- `Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk`.
- `Sheaf.Paper.ComparisonPullbackExact`.
- `Sheaf.Paper.FiniteRingConstructibleSheafOrigin`.
- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`.
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
- `Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity`.
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`.
- `WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension` (duplicate import also removed).
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Homology.ScalarExtensionUnitTriangles`.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.

No module or DAG node is withdrawn. The removed direct imports include interfaces still
named in the plan for the six remaining holes; those mathematical dependencies have not
been pruned from the node. Existing public imports are retained.

## Where the brief, the DAG or earlier work was wrong

No statement correction was necessary. The original node described compatibility with
strict transitions but did not spell out how normalization compatibility passes to
semilinear transitions. The canonical mate's unit law supplies this missing argument;
the eighth step now records it. The landing classifier also requested an explicit
command-scope change record; that record documents the unchanged local command
environment and public API. No second reader or subagent was used.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
