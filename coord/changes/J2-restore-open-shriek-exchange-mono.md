# Restoring open-immersion exchange monicity

## Reason

The assigned `coord/rework.tsv` row records a cluster restoration reverted at 5f7b33eac.
The live module is absent, while quarantine preserves a complete, zero-sorry implementation.
Restore that implementation and its support helpers for the waiting importers.

## Old

The live path
`lean/Sheaf/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/LowerShriek/ExchangeMono.lean`
is absent. Its authoritative source remains at
`quarantine/Sheaf/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/LowerShriek/ExchangeMono.lean`.
The node `stage3-sfb-open-base-change-component-mono` still attaches the public theorem
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange_app_mono`
to that module. There are zero proof holes in the archived file.

## New

Restore the entire archived module byte for byte. Every signature, universe, attribute,
public import, private helper, and proof body remains identical to the archive.
The existing node attachment, proof steps, and dependency list remain unchanged.
No target statement or definition changes meaning; no statement review is reopened.

## Users

A scan of imports in both live roots and both quarantine roots finds these direct consumers.
All three are archived at inspection time. No consumer is edited, so no forced adaptation
or additional claim is needed. Ordinary imports receive the same public theorem, and
import-all consumers receive the same private proof helpers.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | not queried; untouched | Archived direct consumer; identical theorem interface restored. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | not queried; untouched | Archived import-all consumer; identical proof context restored. |
| Sheaf.Paper.CompactificationRefinementLocalizing | not queried; untouched | Archived import-all consumer; all seven shared support helpers preserved. |

The source library is untouched. Restoring the archived interface requires no downstream
statement or proof changes. Server single-file compilation passed in 16.7 seconds with
no errors or warnings; the delivery tool supplies the independent probe.

## Status

landed 20261021T021017-L-2691624 2026-10-21 (merge of deliver/J2/Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono)
