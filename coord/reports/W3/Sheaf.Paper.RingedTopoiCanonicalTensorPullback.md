## What changed

Split the ordinary unit-normalization proof into existence and uniqueness interfaces in
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackUnitExistence` and
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackUnitUnique`. The parent theorem combines these
strictly separate parts with a real witness construction. The parent module's derived theorem
remains unchanged.

## Proved and sorry left

The parent `canonicalRingedTensorComparison_unit` is reduced to the existence and uniqueness
parts. The two split declarations `canonicalRingedTensorComparison_unit_exists` and
`canonicalRingedTensorComparison_unit_unique` remain sorry, with nodes
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-existence` and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-uniqueness`. The parent theorem
`ringedTopoiCanonicalDerivedTensorPullback` remains sorry.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The direct proof requires substantial scalar-extension and sheafification infrastructure; the
unit argument is therefore represented by its two independent mathematical parts.

## New nodes

`lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-existence`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-uniqueness` record the postponed parts and their Stacks 03EL
source.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
