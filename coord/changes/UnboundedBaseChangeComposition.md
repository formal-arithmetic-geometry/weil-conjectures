# Sheaf.AlgebraicGeometry.UnboundedBaseChangeComposition

## Reason

The proof adds a private section containing generic local variables and helper lemmas for
unbounded horizontal pasting. The stage-3 preflight classifies the section commands as an
interface change, so this record documents the proof-only interface change. The two public
theorem signatures remain verbatim unchanged.

## Old

The module contained two public theorems with `sorry` proofs and no local `Pasting` section.

## New

The module contains the same two public theorem signatures, now proved. It adds a private
`Pasting` section with local variables for a generic coefficient category and three private
pasting lemmas. The only added import is the proof-only
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.UnboundedBaseChangeComposition | Q1 | proof completed; private helpers are not exported |

## Status

landed 20261018T062851-L-669863 2026-10-18 (merge of deliver/Q1/Sheaf.AlgebraicGeometry.UnboundedBaseChangeComposition)
