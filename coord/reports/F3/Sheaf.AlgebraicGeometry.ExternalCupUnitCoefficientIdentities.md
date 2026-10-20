## What changed

Completed the assigned retirement of
`Sheaf.AlgebraicGeometry.ExternalCupUnitCoefficientIdentities`, listed with kind
`retire` in the current queue and retirement inventory. The human-approved
October 20 hand-off directs replacement by the upstream twin. Listed the duplicate
in `deleted.txt` and repointed `lem-sc-external-cup-unit-coefficient-identities` to
`WeilConjectures.AlgebraicGeometry.ExternalCupUnitCoefficientIdentities`.
The existing theorem signature is verbatim identical, and the proof is the same.
No upstream module or target statement is edited.

`lcompile.py` compiled the upstream twin and its consumer
`WeilConjectures.AlgebraicGeometry.PicardExternalCupUnitComparison` successfully
without warnings. The duplicate also compiled before retirement (with its existing
long-line warning). `rg` and `tools/downstream.py` confirmed zero current duplicate
importers. The upstream root already imports the twin.

Change record:
`coord/changes/retire-external-cup-unit-coefficient-identities-F3.md`.

## Proved and sorry left

Zero holes before retirement and zero afterward. Closed: none. Added: none.
Split off: none. No remaining `sorry` in the retired module.
The existing complete proof of
`AlgebraicGeometry.Scheme.Modules.external_cup_unit_coefficient_identities`
is preserved in the upstream twin; this delivery claims retirement, not a new proof.

## No longer needed

Pruned duplicate module:
`Sheaf.AlgebraicGeometry.ExternalCupUnitCoefficientIdentities`.
Its former consumer already uses the upstream twin, so no consumer import rewrite
is needed. All five imports in the duplicate remain available in the twin; none
of their mathematical dependencies is claimed unnecessary.
No DAG node or unit step is removed. Parent nodes continue to use
`lem-sc-external-cup-unit-coefficient-identities` through its corrected attachment.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a holed module, but the current queue assigns
this zero-hole module as a retirement item. The retirement inventory's consumer
column is stale: the Sheaf PicardExternalCupUnitComparison module is already absent,
and its upstream replacement already uses the twin. The DAG attachment alone
still pointed at the duplicate. The human-approved retirement instruction is the
basis for this withdrawal; zero importers alone is not its justification.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
