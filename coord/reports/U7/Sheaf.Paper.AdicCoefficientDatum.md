## What changed

Filled the five assigned holes in `Sheaf.Paper.AdicCoefficientDatum`.
Transitions are constructed from normalized scalar extension and proved unique on
local pure tensors. Tensor generation gives naturality and the associativity
cocycle. Derived normalization uses the right Kan extension property, preservation
of K-flat resolutions by scalar extension, and comparison on flat-term K-flat
resolutions. Evaluation follows by postcomposing that Kan extension with the exact
restriction right adjoint and comparing with exact tower evaluation; the counit
formula gives uniqueness.

Private helpers package the categorical arguments and tensor calculations. Added
proof imports for K-flat scalar extension, ordinary and derived coefficient
adjunctions, and whiskering. Named the existing ordinary and derived existential
specifications and protected functor calculations from expensive unfolding.
The original derived-category instance bodies and declaration order are preserved.
Both public functor bodies retain their original witness aliases.
The change record is `coord/changes/U7-adic-coefficient-functor-interfaces.md`.
All target statements retain their signatures and mathematical meaning. The module
`Sheaf.Paper.CompletedAdicCoefficientDatum` is unchanged by this delivery.

Repaired the current return for head `7754223355` (reviewer `C-77542`).
The mathematical review passed; landing failed while reading the absent
`Sheaf.Algebra.Homology.DerivedCanonicalFiltration` source. Its current
`coord/rework.tsv` row preserves it in quarantine. This packet does not alter
or withdraw that module, its node, or its dependencies. The retained Lean
proof has been compared with the current shared item, compiled against the
current published server build, and its consumer/holder table regenerated
from the current source. `deliver3.py` creates the replacement commit on
freshly fetched `sheaf-dag` and runs the server preflight before pushing.

## Proved and sorry left

Closed all five original holes:

- `AlgebraicGeometry.Scheme.completedReductionTransition_exists`
- `AlgebraicGeometry.Scheme.reductionBalance_naturality`
- `AlgebraicGeometry.Scheme.reductionBalance_cocycle`
- `AlgebraicGeometry.Scheme.completedReductionDerivedNormalization_exists`
- `AlgebraicGeometry.Scheme.completedReductionEvaluation_exists`

No holes remain in the item. No holes were added and no statements were split off.
The already-imported `completedAdicBalance_exists` remains an existing dependency
in `Sheaf.Paper.CompletedAdicCoefficientDatum`. Its prerequisites are now proved
in the current published build: all five assigned proofs have only standard axioms.
The existing complete proof of `completedReductionTower_exists` was repackaged
through a general resolving-class argument to avoid unfolding the concrete tower
inside localization calculations.

Validation on the current published server build: the complete module compiles
in 40.6 seconds without warnings. Separate `rfl` checks confirm that the ordinary and derived functors equal their original witnesses.
`#print axioms` lists only `propext`, `Classical.choice`, and `Quot.sound` for
all five assigned proofs. The earlier report of transitive `sorryAx` for the
three balancing-dependent proofs is superseded by this current-build check.
The retained earlier checks compiled the original integral-pullback consumer in 39.4 seconds and all 13 then-identified interface
users. Those retained consumer checks compiled all seven currently identified
textual interface users unchanged against the sandbox item: `CompletedTowerPullback` (8.7 seconds),
`ConstantTowerDirectImageNormalization` (29.9), `FourCorners` (12.5),
`ProEtaleConstantReductionTower` (45.7), `QuotientCornerFrobeniusStructures` (46.4),
`CompletedConstantCoefficientEquivalence` (32.0), and `PbcCompletedPullbackActual`
(25.3), all under `Sheaf.Paper`. No consumer is adapted.

## No longer needed

None. No existing import, module, or required unit step is withdrawn. The proof
uses the supplied coefficient, tensor, K-flat resolution and derived-functor
interfaces. The updated node records the actual dependencies, including the
ordinary and derived coefficient adjunctions.

## Where the brief, the DAG or earlier work was wrong

The node had no numbered proof steps, although its statement described the needed
constructions. Its proof field now records the argument implemented here.
The existing balancing existence theorem is in the completed-coefficient module,
while its docstring cites this same adic-coefficient node. The proof continues to
use that supplied declaration; it does not create a duplicate balancing theorem
or add a dependency on the reduction-model node, which would make a DAG cycle.
No mathematical statement is disputed or weakened. Repeated expansion of the
existential specifications and canonical localization/functor constructions was
too expensive; named predicates and local proof interfaces address that issue.

The current failed landing read a source removed from the active tree by
quarantine. The item itself is present and its dependency imports resolve in
the current server build. The quarantined filtration is absent from the current
353-module downstream query for this item, and no restoration or withdrawal of
that separately assigned module is part of this repair.
Preflight additionally identified `PbcUniformCompleteTriangulated` as a textual
user of `reductionDerivedExistence` outside that downstream query. It is now
included in the change record (354 modules total); its derived specification
is unchanged definitionally, so no consumer edit is needed. The earlier return's
change-record loader naming issue is recorded in the change record.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
