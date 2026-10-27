## What changed

Completed `towerLimit_push_acyclic` by choosing a K-injective resolution of the
levelwise pushforward, applying the completed-tower acyclicity input, and
cancelling the resulting invertible map using naturality of `target.limit.unit`.
The proof-only imports are `Sheaf.Paper.CompletedCoefficientTowerLimitAcyclicAux`
and `Sheaf.Paper.CompletedCoefficientTowerLimitAcyclicResolution`. These
modules contain the two strictly simpler split statements required by the
proof: K-injective resolution existence and preservation of the resolution
quasi-isomorphism by inverse limit.
The zero-morphism instances needed by both statements are declared once in the
acyclicity module and imported by the resolution module.

## Proved and sorry left

Proved `WeilConjectures.CompletedCoefficientPushforward.towerLimit_push_acyclic`.
The two auxiliary modules add two named sorries, both with source and proof
plans in their docstrings and DAG nodes:

- `completedTower_exists_isKInjective`;
- `towerLimit_push_acyclic_aux`.

Thus one item-level sorry was closed and two strictly simpler proof steps were
split off.

The returned declaration collision was repaired by removing the duplicate
resolution-module zero-morphism instances and reusing the declarations imported
from `CompletedCoefficientTowerLimitAcyclicAux`.

## No longer needed

The proof does not use the previously listed dependencies
`lem-weil-pbc-site-equivalence-sheaf-transport` or
`lem-weil-ringed-tower-pushforward-limit-acyclic`, nor their proof imports
`Sheaf.CategoryTheory.ContinuousRingedToposModuleDirectImage` and
`Sheaf.CategoryTheory.RingedTowerPushforwardLimitAcyclic`.

## Where the brief, the DAG or earlier work was wrong

The original DAG route expanded site equivalence transport and the generic
ringed-topos acyclicity theorem before exposing the elementary normalized-unit
cancellation. The completed-model proof only needs the two specialized
intermediate statements recorded here; the target statement itself is unchanged.

## New nodes

`lem-pur-completed-coefficient-tower-limit-acyclic-resolution` records the
K-injective resolution step. `lem-pur-completed-coefficient-tower-limit-acyclic-aux`
records inverse-limit preservation of the pushed resolution quasi-isomorphism.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
