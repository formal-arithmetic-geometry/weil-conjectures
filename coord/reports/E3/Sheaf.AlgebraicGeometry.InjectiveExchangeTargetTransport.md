## What changed

Completed the zero-hole retirement repair for
`Sheaf.AlgebraicGeometry.InjectiveExchangeTargetTransport`.
Withdraw the duplicate module via `deleted.txt` and remove its only remaining import
from the unclaimed `Sheaf.AlgebraicGeometry.InjectiveExchangeRepresentative`.

Move the retired module's three fully proved private helpers verbatim into the consumer:
`assemble_transport`, `exchange_localization_prefix`, and
`target_unit_representative_transport`. The consumer already imports all their comparison
APIs and already sets up the complex, representative isomorphism, functors and square.
Its proof now assembles the localization-prefix and target-unit equalities directly,
then supplies the result to its original `assemble_exchange` argument. The two files'
combined 491 lines become 376 lines. No import is added.

The consumer's public theorem signature, public imports and docstrings are byte-for-byte
unchanged. Its proof still uses the original small-colimit-model structural map and
retains the target derived unit. There is no new public declaration or definition.
Change record: `coord/changes/E3-retire-injective-exchange-target-transport.md`.
No source-library file, target statement or quarantined source changes.

## Proved and sorry left

This is a retirement repair, with zero original holes: closed 0 of 0; added 0; split off 0.
The retired `AlgebraicGeometry.Etale.injectiveExchange_target_transport` had no sorry.
Its private component calculations and the consumer's
`AlgebraicGeometry.Etale.injectiveExchange_representative` remain fully proved.
Every delivered private declaration has a complete proof; no sorry body is present.
The adapted consumer compiles cleanly with `lcompile.py` in 48.8 seconds.

The separately named `AlgebraicGeometry.Etale.smallModel_injectiveExchange_target_transport`
(node `lem-weil-pbc-injective-exchange-target-transport`) also remains fully proved and
unchanged in its existing module. No mathematical obligation is deleted or handed off.

## No longer needed

Pruned `Sheaf.AlgebraicGeometry.InjectiveExchangeTargetTransport` and its public transport
wrapper. Removed its one private import from
`Sheaf.AlgebraicGeometry.InjectiveExchangeRepresentative`. The necessary generic
comparison calculations are retained in the consumer's private proof implementation.
No other module or mathematical node is claimed pruned.

A full attachment scan finds no DAG node attached to the retired module. Node
`lem-weil-pbc-injective-exchange-target-transport` already points to the retained
`StrictLocalSmallModel.InjectiveExchangeTargetTransport`; its only DAG parent,
`lem-weil-pbc-injective-exchange-representative`, already points to the corresponding
small-model representative module. Both realizations, the parent dependency and all
proof steps remain intact, so no node edit is needed. `sk-prop-h2` has neither node
among its realized statement or proof steps, and no unit or chapter route changes.
The quarantined `StrictLocalDerivedExchangeLeray` imports the preserved consumer,
whose original public theorem remains available with exactly the same signature.
A scan of active and quarantined sources finds no remaining import of the retired item.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief does not identify this as a zero-hole retirement, but the current
`coord/retire-items.tsv` and queue do. The retirement table's "same statements" description
is stale: the adopted twin uses `Scheme.strictLocalizationToBase`; the assigned theorem
and its consumer use `Scheme.strictHenselizationStructuralMap`. An import-only replacement
with the adopted twin fails with an application type mismatch at the consumer's original
line 160. The direct comparison proof removes the duplicate while preserving the consumer's
mathematics and the restored DAG's original-model realizations.

LeanFinder, Loogle and Mathlib/source searches confirmed the existing localization and
unit comparison APIs. The retained private calculations use those APIs without assuming
acyclicity of the pulled-back complex or inverting the target unit. No new node,
construction, proof hole or unsupported data choice is introduced.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
