## What changed

Added the degreewise theorem `exchange_restrictScalars_component` and proved the existing
complex-level theorem `exchange_restrictScalars` by extensionality on degrees, site objects,
and sections. The existing `openResMap_isIso` remains unchanged.

## Proved and sorry left

Proved `exchange_restrictScalars`.
The component calculation was split out as `exchange_restrictScalars_component` and remains a
named theorem with `sorry` (node `lem-cbc-finite-open-exchange-scalars-component`).
The pre-existing `openResMap_isIso` remains `sorry` (node `lem-cbc-finite-open-exchange-scalars`).

## No longer needed

No imports or declared proof dependencies were removed. The complex theorem now uses only the
new degreewise component node from its proof route.

## Where the brief, the DAG or earlier work was wrong

The original DAG bundled the degreewise mate calculation and its cochain-complex lift into one
hole. The lift is a routine extensionality argument, so the degreewise calculation is recorded
as a strictly lower split node.

## New nodes

`lem-cbc-finite-open-exchange-scalars-component` records the degreewise scalar-exchange
calculation used by the proved complex theorem.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
