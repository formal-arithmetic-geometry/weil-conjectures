# proEtale_immersion_inverseImage_preservesLimits proof scope

## Reason

Preflight classifies the added proof-scope variable and local elaboration commands as
an interface change. They support private limit-preservation helpers. Every
existing declaration signature and public import is unchanged. No target meaning changes.

## Old

No section variables in the original item module.

## New

The private scalar-extension limit-preservation helper uses:

```lean
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
```

The private abelian comparison also uses command-local backward elaboration settings.
These commands only elaborate the following private declarations. A proof-only
`import all Sheaf.AlgebraicGeometry.ProEtaleOperations` accesses its already proved
private adjunction and scalar equivalence; no new instance or declaration is exported.
The final theorem binds its own schemes and morphism explicitly; no signature changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation | D2 | Private proof helpers added; existing signature unchanged. |
| All importers of this module | unchanged | Public imports and existing signatures unchanged; no adaptation needed. |

## Status

landed 20261015T233748-L-3369032 2026-10-15 (merge of deliver/D2/Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation)
