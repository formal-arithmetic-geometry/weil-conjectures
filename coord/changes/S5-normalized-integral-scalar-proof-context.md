# WeilConjectures.normalizedIntegralScalarCoherence

## Reason

The command-diff advisory classifies proof-context commands as potentially visible.
The delivery adds private categorical helpers and their scoped variables. It uses
`synthInstance.maxSize 4096` and the three instance exclusions already in the
publicly imported `IntegralComparisonSystemData`; no existing instance changes.
The original public section and exact theorem signature are retained. The private
helpers occupy `noncomputable section Proofs`, closed before the public theorem.
No definition or public theorem statement changes.

## Old

```lean
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
```

The existing public theorem had a `sorry` proof and no private helpers.

## New

```lean
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

noncomputable section Proofs
```

`Proofs` closes before the existing theorem. `Coordinates` within it scopes the
parameters of the private proof lemmas. Every new helper in this module is private
and fully proved. The existing signature and public import are verbatim unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SimultaneousIntegralPullbackComparisons | unclaimed in shared records | Direct importer; exact public statement and existing instances retained; no adaptation. |

This is documentation of a syntactic advisory, not an interface repair. No shared
definition, statement, binder, attribute on an existing declaration, reducibility,
simp rule, or instance interface changes; no consumer adaptation is required.

## Status

landed 20261027T094515-L-236295 2026-10-27 (merge of deliver/S5/Sheaf.Paper.NormalizedIntegralScalarCoherence)
