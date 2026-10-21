# AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange_app_section

## Reason

The assigned rework row records a cluster restoration reverted at 5f7b33eac.
The live ExchangeSection module is absent; quarantine preserves its complete zero-hole proof.
Restore the attached theorem for the archived lower-shriek base-change consumer, using
ExchangeMono's already proved shared unit helper instead of duplicating its derivation.

## Old

The live path
`lean/Sheaf/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/LowerShriek/ExchangeSection.lean`
is absent. The authoritative archived source is
`quarantine/Sheaf/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/LowerShriek/ExchangeSection.lean`.
The existing node `stage3-sfb-open-base-change-component-section` retains its Lean attachment.
The archived theorem has zero sorry holes.

## New

Restore the archived module, retaining its complete theorem signature, docstrings, public
import and proof-only import-all of ExchangeMono. Replace the repeated proof of unit
invertibility with `have := sharedBoundedOpenUnitIsIso Λ ℓ j`. Retain the cartesian counit
proof input and the componentwise inverse construction. The DAG records reuse of both
proved helpers from ExchangeMono. No definition, instance, target or statement changes.

## Users

The live tree has no direct importers of the absent module. Scanning both live roots
and both quarantine roots finds the single archived direct consumer below. Its proof
passes the same exchange formula by reflexivity; the exact restored signature remains
compatible. No consumer is adapted and no source-library file is changed.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed at inspection; archived | Identical component-section theorem interface restored; no adaptation. |

The archive and existing DAG attachment remain intact. No target statement review is
reopened. Server single-file compilation of the restored and simplified file passed
without errors or warnings in 2.9 seconds; delivery runs the independent axiom probe.

## Status

landed 20261021T021924-L-2793148 2026-10-21 (merge of deliver/P3/Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection)
