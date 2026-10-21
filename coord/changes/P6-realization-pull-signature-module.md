# WeilConjectures.RealizationCompletedPullData

## Reason

Move the unchanged data declarations to a shared signature module so proof dependencies can
use them without importing the existence theorem whose proof uses those dependencies.

## Old

In `Sheaf.Paper.RealizationCompletedPull` (the signature, verbatim):

```lean
def RealizationCompletedPullData (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (k : Type u) [Field k] : Prop
```

The other 31 data declarations preceding this definition are moved with it verbatim.

## New

In `Sheaf.Paper.RealizationCompletedPullData` (the same signature):

```lean
def RealizationCompletedPullData (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (k : Type u) [Field k] : Prop
```

All 32 data declarations and their complete bodies are copied verbatim.
`Sheaf.Paper.RealizationCompletedPull` publicly imports that module. Every declaration
name, type, definition body, instance attribute and public import remains available.
The existence theorem has its original signature. No target meaning changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RealizationCompletedPull | P6 | Proof rewritten; original interface forwarded. |
| Sheaf.Paper.RealizationAdjointComparisons | unclaimed | Public import forwarding preserves all uses; no edit. |
| Sheaf.Paper.RealizationPullOrdinarySystem | new, P6 | Uses shared signatures. |
| Sheaf.Paper.RealizationPullRationalDescent | new, P6 | Uses shared signatures. |

The read-only downstream scan on 2026-10-21 found the one existing importer listed above.

## Status

landed 20261021T183350-L-1608812 2026-10-21 (merge of deliver/P6/Sheaf.Paper.RealizationCompletedPull)
