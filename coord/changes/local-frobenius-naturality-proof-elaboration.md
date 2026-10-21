# WeilConjectures.localFrobeniusWeilMorphismNaturality

## Reason

Preflight conservatively flags the added `open scoped` and `attribute` commands as
interface changes. They support the private proof helpers only. Tensor notation is
needed to use the published pure-tensor pullback prescription. Local irreducibility
prevents expensive unfolding while elaborating the equality-transport and final
specialization proofs. The complete module compiles cleanly in 20.4 seconds with the
normal heartbeat and single-file time limits. No definition, signature, public import,
instance, or exported attribute is changed.

## Old

The module had no scoped TensorProduct opening and no local irreducibility attributes.
All existing declaration signatures and definition bodies are retained verbatim.

## New

```lean
open scoped TensorProduct
attribute [local irreducible] rationalDerivedPullback
attribute [local irreducible] pointRationalFibre localPointTransportIterate localWeilIterate
  localConstructibleReturnComparison localConstructibleReturnTransport localExtensionFrobenius
```

The `local` attributes are confined to this file. The notation opening does not export
notation or alter its meaning for importers. New helpers are private proved theorems.
The only removed import is the proof-only import
`Sheaf.Paper.IntegralPullbackComparisonRealization`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality | H1 | Private proofs elaborate without unfolding large definitions; public signatures and definitions unchanged. |

The source scan finds no current direct Lean importers. This does not withdraw the item:
its parent DAG dependencies and unit route remain. No consumer adaptation is required
because these commands are local proof elaboration support and the public interface is
unchanged. The downstream scan is also recorded in the report.

## Status

landed 20261021T193345-L-1127053 2026-10-21 (merge of deliver/H1/Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality)
