## What changed

Proved `WeilConjectures.rationalTensorStageComparison_coherent` in
`Sheaf.Paper.RationalTensorStageCoherence`.
The public definition, theorem statement and three public imports are unchanged.
The new generic module `Sheaf.CategoryTheory.BilinearStageTowerTransport` uses
a private `import all Sheaf.CategoryTheory.BilinearCoefficientDescent` to prove
transport across equal transition and associator data. The item imports that
proved API normally, keeping hidden categorical proof bodies out of the
geometric module.

The proof identifies the two normalized completion comparisons by uniqueness,
cancels completion isomorphisms in the ordinary tensor tower, restricts to the
constructible categories, applies rational localization and substitutes the
recorded stage equalities. The finite-field rational tower equation is proved in
the new module
`Sheaf.Paper.RationalTensorTowerCoherence`; its calculation helpers are private.
The main module privately imports this proved equation.
The existing node's proof steps now describe these exact calculations.

The coefficient-stage proof transports the whole `TensorTowerDatum` along its
equality with the raw finite-field datum. Its `Coherent` predicate is exactly
the tensor-tower component equation. Keeping category structures, functors and
comparisons in this record avoids reducing specialized morphism compositions
while changing the category presentation.
The proof caches typed stage functors and comparisons in private definitions
to reuse their checked interfaces. No coefficient model or algebra structure changes.

Validation: all four modules compile cleanly through `lcompile.py --all`.
The original public definition and theorem signature, and both original private
helpers used by the parent module, were checked against the restored source
and are preserved verbatim. No debug or profiling settings remain.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.rationalTensorStageComparison_coherent`
(node `lem-weil-rational-tensor-stage-coherence`).
Added 0 holes. No `sorry` remains in any of the four delivered modules.
Also proved `CategoryTheory.BilinearCoefficientDescent.familyTower_of_transport`
(node `lem-weil-bilinear-stage-tower-transport`) and
`WeilConjectures.rationalTensor_tower`
(node `lem-weil-rational-tensor-tower-coherence`). The ordinary tower
lemma used by the proof is an existing declared dependency, not a new split.

## No longer needed

No modules or mathematical dependencies are pruned. No original import is removed.
The temporary private `import all Mathlib.Logic.Small.Defs` was removed after
successful compilation without it. The main node now reaches
the integral and rational calculation through the new proved tensor-tower node.
The rational tower module imports finite rational operations, scalar
composition and the generic tensor-tower datum. It does not require
coefficient stages or bilinear descent.
The original private helpers `tensorStageComparison_endpoint` and
`tensorDescent_with_components` are retained verbatim: the parent module
`Sheaf.Paper.DerivedPullbackTensorHom` uses them through `import all`.
The original node's Lean attachment is preserved. Its mathematical dependencies
remain reachable through the proved helper nodes.

## Where the brief, the DAG or earlier work was wrong

The source was absent from `lean/` because of its recorded quarantine, not
because its statement was withdrawn. The sandbox source was copied from the
current archive; the shared repository restored its sources during this session.
No mathematical statement or definition was changed. The bilinear descent
module marks `FamilyTower` as `no_expose`, so unfolding it requires a private
`import all`; the existing public import alone does not expose its body.

The unchanged direct consumer `Sheaf.Paper.DerivedPullbackTensorHom` completed
Lean checking but exceeded the time gate at 63.9 seconds against this proof.
A baseline check of the same parent source against the original unproved item
also exceeded the gate, at 77 seconds. Both used the private-overlay pullback
modules (cached in the baseline run). Neither reported an elaboration or kernel
error. This is an existing timing issue in the consumer held by E3; no consumer
is adapted or included in the packet. The assigned item itself passes the
60-second check. The temporary consumer copy and baseline item were removed;
the completed item is restored.

## New nodes

`lem-weil-rational-tensor-tower-coherence`, realized by
`WeilConjectures.rationalTensor_tower` in
`Sheaf.Paper.RationalTensorTowerCoherence`, is the finite-field part of the
original proof plan. It states the normalized rational tensor equation before
recorded stage-system transports. It is fully proved, with no new hole. The
remaining stage transport is proved in the assigned module. No existing public signature, definition, or public import changed.
`coord/changes/N1-rational-tensor-stage-proof.md` explains the static command
heuristic advisory and documents the unchanged consumer interface.

`lem-weil-bilinear-stage-tower-transport`, realized by
`CategoryTheory.BilinearCoefficientDescent.familyTower_of_transport` in
`Sheaf.CategoryTheory.BilinearStageTowerTransport`, isolates the elementary
substitution argument for recorded transition and associator equalities. It is
fully proved. It consumes coherence of the actual data record.
Isolating its private body import avoids loading the hidden
categorical proof facet into the large geometric module.



`def-weil-tensor-tower-datum`, realized by `CategoryTheory.TensorTowerDatum`
and its `Coherent` predicate in `Sheaf.CategoryTheory.TensorTowerDatum`, packages
the existing category structures, six functors and four comparison isomorphisms.
`Coherent` is the original component equality, universally quantified over the
two inputs. The record adds no hypothesis and contains no proof field or choice.
This representation lets the stage proof transport data before exposing the
component equation, avoiding the slow reduction of specialized coefficient
structures.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
