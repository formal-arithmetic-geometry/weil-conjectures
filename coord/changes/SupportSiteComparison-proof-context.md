# SupportSiteComparison proof context

## Reason
The proof adds private helper lemmas and local elaboration options to
`Sheaf.AlgebraicGeometry.SupportSiteComparison`. The public declarations and
all existing signatures remain unchanged. The delivery preflight classifies
these commands as changing the module's visible environment, so this record
makes the proof-only context change explicit.

## Old
The module had only `set_option autoImplicit false` and opened
`CategoryTheory`, `CategoryTheory.Limits`, and `Opposite`.

## New
The module retains its declarations and adds local transparency options,
private helper lemmas in `CategoryTheory.Functor`, and the existing proof
imports needed by those lemmas.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | S2 | proof context only; public signatures unchanged |
| downstream importers | various | no declaration or interface change |

## Status
landed 20261019T231333-L-575401 2026-10-19 (merge of deliver/S2/Sheaf.AlgebraicGeometry.SupportSiteComparison)
