# DerivedNakayamaResolution private proof instance scopes

## Reason

The completed proof needs the small-colimit instance supplied by the existing
`hasColimitsOfSizeShrink` theorem. Preflight identified the local instance declaration as a
possible public change and identified one textual consumer. This record documents its
scope and that consumer. All original public imports, signatures, definitions, and existing
instances are preserved verbatim. There is no target-meaning change.

## Old

There was no proof-local small-colimit instance in this module; the main theorem was `sorry`.
The original public API and its imports are unchanged by this delivery.

## New

Inside the private proof-tools section and `UnitScalar` namespace:

```lean
local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A
```

This instance is scoped to that namespace section, which ends before the main theorem.
It supplies the derived-category comparison proofs. The added scalar-ring, linear,
monoidal-linear and pullback-exactness instances are explicitly `private`; their private
names and their implementations occur only in the new proved helpers. No new instance is
exported by the module. In particular the small-colimit instance adds no hypothesis to any
existing public signature.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DerivedNakayamaResolution | D3 | Uses the scoped instance in the proved private reduction-comparison helpers. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Textual hit only: its pre-existing generic hypothesis `[HasColimitsOfSize.{0, 0} A]` is unrelated to the locally scoped instance. No edit or adaptation is required. |

`tools/downstream.py Sheaf.Paper.DerivedNakayamaResolution --uses
'instance : HasColimitsOfSize.{0, 0} A'` reports precisely the second row above. Reading that
module confirms that the match is its own explicitly assumed class, not a reference to a
new declaration. The local instance has no public name. Restoring both original public
imports also preserves all importers' existing environment.

## Status

landed 20261021T060957-L-1681516 2026-10-21 (merge of deliver/D3/Sheaf.Paper.DerivedNakayamaResolution)
