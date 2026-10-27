## What changed

Proved `WeilConjectures.PointTransformationDescent.coefficient_descent` from the three
existing proof dependencies in the DAG. Rational normalization produces the rational
family and its normalized components and scalar equation. The composite-comparison
result supplies unit/tower equations, actual actions, scalar transport, and independence.
The rational-family theorem supplies same-stage naturality and the normalized descended
transformation. The proved private helper `comparison_hom` removes the identity functor associators
in the composite comparison, identifying its component with `rationalB`. The proof
assembles exactly the existing conjunctions, with equality-to-HEq
conversion for the unit and tower hypotheses. The item theorem statement stays unchanged. Duplicated item helpers are now
abbreviations of the existing integral/rational owners, with exactly the same constructions. The parent node records the component calculation and conjunction assembly;
the two repaired dependency nodes explicitly record the canonical coefficient models,
with their sole citer audited as still valid. The composite-comparison import is private. The normalization and common-stage
imports are public because they now own the canonical definitions used by the aliases.

Aligned the indexed predicates in the unclaimed modules
`Sheaf.Paper.PointTransformationRationalNormalization` and
`Sheaf.Paper.PointCompositeComparisonTower` with the canonical small coefficient fields
already used by this item and `PointRationalFamilyCommonStageNaturality`. Literal
`F.val` fields become `Coefficient.{u} l Ω F`, and their inclusion homomorphisms become
`coefficientInclusion`. This is transport along the prescribed Shrink algebra equivalences,
not an additional hypothesis or a weakening. No source-library module is edited.

After an assembly compile exceeded 60 seconds, profiling exposed repeated unfolding
of the duplicate helpers through derived localizations and size transports. The
canonical aliases remove those comparisons without changing their mathematical data.

Change records:
`coord/changes/R4-PointTransformationCoefficientDescent-coefficient-models.md`,
`coord/changes/R4-PointTransformationRationalNormalization-coefficient-models.md` and
`coord/changes/R4-PointCompositeComparisonTower-coefficient-models.md`.
The downstream script reports zero existing consumers for both repaired modules, and
namespace searches find no external uses. The new parent proof is their only consumer.

## Proved and sorry left

Closed one existing hole:
`WeilConjectures.PointTransformationDescent.coefficient_descent`
(node `lem-weil-point-transformation-coefficient-descent`). Zero holes remain in the item.
No holes added or split off.

The two repaired dependencies retain their existing holes:
`WeilConjectures.PointRationalNormalization.rational_normalization`
(node `lem-weil-point-transformation-rational-normalization`) and
`WeilConjectures.PointCompositeComparison.tower_and_actions`
(node `lem-weil-point-composite-comparison-tower`). These are existing DAG obligations,
not new lemmas. The proof also uses the existing theorem
`WeilConjectures.PointRationalFamily.rational_family_common_stage_naturality`, whose
existing hole is in its unchanged module. This is a proof from the stated dependencies;
it does not claim their mathematical arguments are already closed.

Validation: both repaired dependencies compile individually in the packet; the assembled
item compiled in 18.5 seconds. The only warning was an unreachable fallback tactic,
which has been removed. Delivery preflight supplies the final axiom and warning checks.

## No longer needed

Removed the item's unused private imports:
`Sheaf.Paper.IsomorphismDerivedPullback`,
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, and
`Sheaf.Paper.IntegralScalarExtensionUniverses`.
No declared proof dependency or node is pruned: all three planned results are used.
All preexisting public imports are preserved. The canonical helper owners are added
as public imports because the aliases use their definitions. No claim that a removed direct import is globally
unreachable is made: the dependency results may still need it.

## Where the brief, the DAG or earlier work was wrong

The planned three-result assembly was mathematically correct, but two Lean dependencies
used literal finite subfields while their parent and common-stage family used canonical
small coefficient models. These types are algebra equivalent, not definitionally equal.
The repair uses the same canonical models throughout, retaining the prescribed
conjugated inclusions and all equations. Equal fields, identity inclusions, zero maps,
empty sums, and torsion objects remain covered, with no invertibility of the supplied
transformation and no injectivity of coefficient transitions assumed.

The rework table still lists this item and the two dependencies as quarantined after
a projective-line import failure, but all three current source files are restored.
This packet starts from those current sources and preserves their Lean attachments
and mathematical dependencies; no archive or module is withdrawn.

## Forced adaptations

### Sheaf.Paper.PointCompositeComparisonTower
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

### Sheaf.Paper.PointTransformationRationalNormalization
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
