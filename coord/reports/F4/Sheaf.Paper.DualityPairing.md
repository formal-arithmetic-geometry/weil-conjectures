## What changed

Proved `AlgebraicGeometry.Etale.etaleKoszulSymmetry` by constructing the
natural derived localization braiding and transporting its components to the
concrete étale tensor. The proof uses the proof-only helper module
`Sheaf.Paper.DualityPairingHelpers`; its concrete tensor presentation is
recorded as the new node `lem-weil-duality-pairing-etale-tensor-raw`. The ambient
pairing theorem remains unchanged. The visible proof-state change is recorded
in `coord/changes/duality-pairing-proof-helpers.md`.

## Proved and sorry left

Closed `AlgebraicGeometry.Etale.etaleKoszulSymmetry` (1 of 2 original holes).
`AlgebraicGeometry.Etale.ambient_duality_pairing` remains sorry. Added the
strictly lower statement `AlgebraicGeometry.Etale.etaleTensorRaw`, whose proof
is left sorry because the concrete derived-monoidal instance exceeds the
compiler's deterministic kernel time; this is one split-off hole.

## No longer needed

No existing imports, DAG nodes, or library modules were removed. Exploratory
intermediate exactness declarations and nodes were withdrawn before delivery.

## Where the brief, the DAG or earlier work was wrong

The recorded tensor-symmetry route is valid, but reducing the concrete derived
monoidal instance to its raw curried tensor is too expensive for the isolated
compiler. The independent symmetry construction remains short once that
strictly lower presentation lemma is available.

## New nodes

`lem-weil-duality-pairing-etale-tensor-raw` records the split-off concrete
presentation lemma in `Sheaf.Paper.DualityPairingHelpers`.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
