# Sheaf.Paper.NativeCompactSupportFiniteScalarCoherence

## Reason

The target transition identity reduces formally to the integral finite-Tor generator
calculation. The latter is recorded as a strictly smaller stage-3 theorem so the
remaining coefficient-mate calculation has a precise owner and source.

## Old

The target theorem body was `by sorry` and had no proof-only helper import.

## New

The target theorem now destructs a pair object, constructs its finite-Tor integral
representative using `integral_residue_tor`, and applies the generator transition
identity. The helper module
`Sheaf.Paper.NativeCompactSupportFiniteScalarCoherenceGenerator` contains that
strictly smaller generator statement with its own DAG node and documented proof.
The target signature and all public declarations are unchanged.

## Users

No existing consumer is changed. The new module is imported proof-only by the item.

## Effect

One target sorry is closed and one strictly smaller generator theorem remains as a
named sorry. The formal representative reduction compiles independently of the
remaining analytic coefficient calculation.

## Status

landed 20261027T234342-L-111042 2026-10-27 (merge of deliver/V4/Sheaf.Paper.NativeCompactSupportFiniteScalarCoherence)
