# CategoryTheory.finiteFreeCompletionTransport

## Reason

The generic finite-free completion proof does not use the scheme-specific completed-tensor
reflector. Remove its unused public reexport and the unused private dual-limit import.
All four theorem signatures and the remaining public imports stay identical. The new
imports serve only the proofs. This record documents the public-import removal; it is
not a definition or statement change.

## Old

```lean
public import Sheaf.CategoryTheory.SystemScalarCoherence
public import Sheaf.CategoryTheory.RingedKoszulCompletionReflector
public import Sheaf.Paper.WeilCompletedTensorReflector
```

## New

```lean
public import Sheaf.CategoryTheory.SystemScalarCoherence
public import Sheaf.CategoryTheory.RingedKoszulCompletionReflector
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.RationalRealizationScalarCoherence` | G7 | The only direct importer. Its existing private import of `Sheaf.Paper.WeilCompletedTensorReflector` supplies the same proof context independently. No signature, definition or proof adaptation is needed. |

The item's four theorem signatures are unchanged, so their transitive users keep the same
interface. The removed module was publicly reexported only through this item; its only
direct importer uses this item privately, so that reexport did not reach later consumers.
No target definition or target statement changes meaning. No module is withdrawn.

## Status

landed 20261021T204147-L-3959797 2026-10-21 (merge of deliver/Z7/Sheaf.CategoryTheory.FiniteFreeCompletionTransport)
