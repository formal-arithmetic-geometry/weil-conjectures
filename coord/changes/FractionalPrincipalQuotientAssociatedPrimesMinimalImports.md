# Sheaf.RingTheory.FractionalPrincipalQuotientAssociatedPrimesMinimal imports

## Reason

Mathlib.RingTheory.Ideal.Height is needed only by the proof. Its explicit public
import is redundant: AssociatedPrime.Basic supplies minimalPrimes for the statement,
and the proof-only height sibling supplies the height lemmas. Removing the redundant
public import follows the stage-3 import visibility rule. No declaration changes.

## Old

```lean
public import Mathlib.RingTheory.Ideal.Height
```

## New

The explicit import is removed. The height interface remains available to this proof
through `import Sheaf.RingTheory.FractionalPrincipalQuotientAssociatedPrimesHeight`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.FractionalPrincipalQuotientAssociatedPrimes | unclaimed | No statement or proof changes: it already publicly imports Mathlib.RingTheory.Ideal.Height. Its original file compiles against the delivered module. |

This is the only direct importer (tools/downstream.py --direct). All 214 transitive
importers pass through it; since its own public imports retain Height, their available
interfaces and statements are unaffected. The theorem signature is byte-for-byte
unchanged. No target definition changes, and no forced adaptation is needed.

## Status

landed 20261013T024037-L-3335296 2026-10-13 (merge of deliver/J3/Sheaf.RingTheory.FractionalPrincipalQuotientAssociatedPrimesMinimal)
