## What changed

Proved AlgebraicGeometry.ProEtale.SpTowerShriek.geometry_adjunction_evaluation
from the generic Geometry.unit_evaluation and Geometry.counit_evaluation fields.
Three proved private helpers project and derive adjunction-package equalities and
transport the two evaluation equations. They take the needed projections as
arguments, avoiding dependent elimination of the full large geometry records.

Repaired Geometry.levelAdjunction_eq in SmoothPurityTowerShriekData to identify
both ordinary functors together with their ordinary adjunction as a dependent
pair. This is the missing constant-coordinate normalization required by the proof;
it does not assume either evaluation conclusion. The correction is recorded in
coord/changes/C4-tower-level-adjunction-coordinates.md, including all 527 transitive
consumers and their current published holders. No source-library file is changed.

The item now imports SmoothPurityTowerShriekData directly. The only direct importer,
TowerCompactSupportProjectionFormula, already explicitly imports the former
SmoothPurityTowerShriekLevels reexport. Updated both affected DAG records.

## Proved and sorry left

Closed one hole: AlgebraicGeometry.ProEtale.SpTowerShriek.geometry_adjunction_evaluation
(lem-sp-tower-geometry-adjunction-evaluation). The item had 1 sorry and has 0.
Added 0 holes and split off 0 statements. SmoothPurityTowerShriekData has 0 sorries.
There is no sorry in either delivered Lean file, including all private helpers.

The existing strictSystemGeometricRealization dependency remains unfinished. Its
coordinate-construction obligation now explicitly retains the two finite functor
parameters; this normalization repair is not claimed to follow from the old
adjunction-only HEq. Its existing proof plan constructs those actual canonical
constant-section operations. No hole in that dependency is claimed closed here.

## No longer needed

Removed the item's public import of Sheaf.Paper.SmoothPurityTowerShriekLevels,
replacing it with Sheaf.Paper.SmoothPurityTowerShriekData. Removed
det-sp-tower-shriek-levels from the item's statement and proof dependencies:
the assertion is conditional on b and g, so it does not use existence of the
compact-support laws. Its actual interface dependency is def-sp-tower-shriek-data.
The generic semilinear-derived-sections dependency is retained. No module is
withdrawn or globally pruned; the parent projection proof still imports Levels.
No tensor, projection-invertibility, compactification or constructibility lemma is
used by the evaluation proof. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original proof plan said to transport through levelAdjunction_eq, but that
HEq compares adjunction values without identifying their two functor parameters.
Lean reports dependent elimination failure on the equation between those
Adjunction types. Bundling both functors with the ordinary adjunction fixes the
interface rather than assuming a new evaluation law. The record gives the old
and new signatures and the direct consumer audit; no existing Geometry constructor
or projection consumer needs adaptation. The internal coordinate witness is
stronger as a formal requirement, matching the stated constant-section intent.
No target statement is edited. Geometry does not occur in a Challenge signature;
any target definition found to depend on this internal datum needs the usual
independent statement review.

The first implementation unpacked the entire geometry records and hit the kernel
limit. Passing only the needed projections removes that expansion; profiling
showed 245 ms of cumulative type checking for the resulting module. Debug options
are removed before delivery.

Validation: both changed modules and the six consumer versions copied at the
start of validation compiled in the same overlay. The theorem's axiom check
reports exactly propext, Classical.choice and Quot.sound. A concurrent proof
landing changed SmoothPurityTowerLocalization after the copies were prepared;
its temporary validation copy is removed, preserving the new shared proof.
No validation source copies or debug commands remain in the delivered packet.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
