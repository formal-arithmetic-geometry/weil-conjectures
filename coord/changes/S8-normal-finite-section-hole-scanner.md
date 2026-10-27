# Normal finite-section warning-option repair

## Reason

The reviewer approved delivery a06011f4958, but landing refused an unattributed hole
at line 26. The source-only hole scanner treats the suffix of `warn.sorry` as a
hole. Remove the inherited warning-suppression command from
`Sheaf.SecPurity.NormalLocallyConstantFiniteSection`. The command scanner classifies
this file-level option removal as an interface change and requires this record.
The option controls diagnostics; it changes no mathematical statement or construction.

## Old

The item contained these commands:

```lean
set_option autoImplicit false
set_option warn.sorry false
```

Its original theorem had one named hole. The reviewed packet replaced that proof
by the representability, nonemptiness and finite-cover evaluation argument, with
one separate geometric universe-descent theorem hole.

## New

The item retains `set_option autoImplicit false` and removes the warning option.
It has no literal holes. The new module
`Sheaf.AlgebraicGeometry.NormalGeometricCoverUniverseDescent` retains exactly the
named public theorem hole `AlgebraicGeometry.normalGeometricCover_universeDescent`.
Its signature, node and proof in words are unchanged from the reviewed packet.
All existing public theorem signatures and public imports are preserved. Private
proof imports and helpers are as in that packet. No existing definition changes.

## Users

`tools/downstream.py Sheaf.SecPurity.NormalLocallyConstantFiniteSection --uses
exists_finiteEtale_section_of_normal_locallyConstant` lists three downstream modules;
none currently mentions the theorem by name outside the item itself.

| Module | Effect |
| --- | --- |
| Sheaf.SecPurity.NormalLocallyConstantFiniteSection | S8 item: diagnostic option removed; server compile passes. |
| Sheaf.Paper.NormalLatticeFiniteCoverPresentation | Existing theorem and public imports unchanged; no consumer adaptation needed. |
| Sheaf.Paper.NormalProEtaleMonodromy | Existing theorem and public imports unchanged; no consumer adaptation needed. |
| Sheaf.Paper.TameIntegralReductionFamily | Transitive consumer; no changed statement or definition and no adaptation needed. |

The newly added geometric statement is used only in the item's proof through a
private import. No target type or definition used by a target is changed. No module
held by another group is edited by this delivery.

## Status

landed 20261023T135343-L-2877310 2026-10-23 (merge of deliver/S8/Sheaf.SecPurity.NormalLocallyConstantFiniteSection)
