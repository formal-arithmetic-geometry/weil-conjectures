# Mathlib.RingTheory.Finiteness.Basic import

## Reason
The proof needs the existing finite quotient instance, which is defined in the Basic module. It is proof-only and therefore is now a private import.

## Old
`public import Mathlib.RingTheory.Finiteness.Defs`

## New
`public import Mathlib.RingTheory.Finiteness.Defs`
`import Mathlib.RingTheory.Finiteness.Basic`

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.GlobalDimensionFiniteModules | Q3 | proof-only import |

## Status
landed 20261012T194134-L-462645 2026-10-12 (merge of deliver/Q3/Sheaf.RingTheory.GlobalDimensionFiniteModules)
