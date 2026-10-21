## What changed

Proved `AlgebraicGeometry.Scheme.StrictScalarBalancing.quotientDiagramScalarProjection`
without changing any existing signature, public import, or definition. Its projection
identity follows from the actual mate definitions, the supplied balancing equation,
counit naturality, and injectivity of the diagram adjunction Hom bijection.

The independent scalar invertibility step is a separate new theorem in
`Sheaf.Paper.StrictQuotientScalarDirectIsomorphisms`, also fully proved in this delivery.
Its private helpers construct normalized derived right adjunctions, transport them
to supplied right adjoints, and verify the mate on K-injective representatives.
The ordinary module mate is invertible by its underlying insertion normalization;
whiskering gives the tower mate. Flat scalar extension makes restriction preserve
K-injectives, so the ordinary calculation derives to the two required mates.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.Scheme.StrictScalarBalancing.quotientDiagramScalarProjection`.
One of one original holes closed; no holes added or left in the packet.
The separate theorem
`AlgebraicGeometry.Scheme.StrictScalarBalancing.strictQuotientScalarDirectIsomorphisms`
is fully proved, as are all its private helpers. There is no unfinished split-off result.
Existing imported named theorems are used as the stage-3 dependency contract permits.
An explicit axiom audit of the scalar theorem still lists `sorryAx` through those
existing dependencies, including `ordinaryPullComparison_existsUnique`; this is
not yet an axiom-clean proof of the entire imported closure. The packet adds no axiom
or hole.

The final packet compiles without warnings: the scalar module in 24.7 seconds,
the assigned projection module in 6.6 seconds (lcompile --all).

## No longer needed

Removed the following private imports from the assigned module:

- `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`
- `Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization`
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
- `Sheaf.Paper.CompletedConstantAlgebraFlatQuotients`
- `Sheaf.Paper.ReductionPullbackDerivedTower`
- `Sheaf.CategoryTheory.RingedTopoiCanonicalTensorPullbackOfUniverses`

The projection calculation does not use
`lem-weil-pbc-reduction-pullback-derived-tower`,
`lem-weil-pbc-augmented-diagram-projection-mate`,
`def-weil-pbc-projection-formula-map`,
`lem-weil-pbc-constant-tower-pushforward-normalization`, or
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` as proof lemmas: its maps
and square are already the published mates and supplied balancing equation.

The scalar proof also avoids `lem-weil-pbc-flat-ringed-diagram-restriction`,
`lem-weil-pbc-diagram-site-realization`, `lem-pe-constant-left-module-inverse-image`,
and `lem-weil-pbc-profinite-coefficient-inverse-image` as direct proof lemmas.
Normalized module adjunctions and the supplied scalar-insertion equation give the
ordinary calculation directly; whiskering and K-injective representatives give the
strict tower calculation. Flatness is obtained through the published coefficient API.
No whole module is withdrawn and no global pruning is claimed: the omitted local
dependencies may still occur transitively or elsewhere. The unit route stays intact.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface change was needed. The original DAG's repeated
representative identifications for the projection equation were already encoded
in its definitions and `PullCompatibility`. Invertibility of a left comparison
alone does not prove invertibility of its right mate. The separate scalar proof
uses the normalized insertion and derived adjunction equations and flatness.

Local opacity for completed coefficients, module pullback and insertion, and exact
derived restrictions avoids expanding their constructions during abstract rewrites.
Using `DerivedPullComparisonFormula` directly in the private derived-mate helper
avoids an expensive conversion at the final tower computation equation. No compile
limit was raised, and the proof was not split into files for performance.

## New nodes

`lem-weil-pbc-strict-quotient-scalar-direct-isomorphisms` records the independent
flat scalar setup from the original node's Step 1. It is strictly smaller than the
assigned conjunction, omitting its entire quotient projection identity, and is
fully proved here. Its module is `Sheaf.Paper.StrictQuotientScalarDirectIsomorphisms`.
The recorded searches cover LeanFinder, Loogle, grep and LeanSearch; no exact existing
statement was found. The node now follows the ordinary mate and K-injective proof.
No existing statement, definition, public import, or unit record changes, so no
change record or forced adaptation is required.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
