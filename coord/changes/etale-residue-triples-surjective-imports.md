# Sheaf.RingTheory.EtaleResidueTriplesSurjective imports

## Reason

The item theorem and its proof do not use `Mathlib.CategoryTheory.Filtered.Basic`.
Removing the public re-export makes the module's interface match its declarations.

## Old

`public import Mathlib.CategoryTheory.Filtered.Basic`

## New

The import is removed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.StrictHenselizationTriples | R1 | It already publicly imports `Mathlib.CategoryTheory.Filtered.Basic`; no adaptation is needed. |

## Status

landed 20261012T070536-L-3470601 2026-10-12 (merge of deliver/F2/Sheaf.RingTheory.EtaleResidueTriplesSurjective)
