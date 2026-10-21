# AlgebraicGeometry.Scheme.exists_properFlatDirectImagePerfectChart

## Reason

Restore the zero-hole quarantined module listed in coord/rework.tsv. Its original import
of the retired Sheaf derived-pullback module no longer exposes derivedPullback or
its specification; the original file fails with unknown identifiers at lines 80 and 119.
The adopted source module is the current owner recorded in def-pc-derived-pullback.
Redirecting that public import repairs the error; the archived proof compiles unchanged.
No definition, theorem signature, hypothesis, conclusion or target meaning is changed by
this delivery. The previously adopted derived-pullback definition is used via its proved API.
No source-library file is modified. The sole archived caller needs the identical public-import
repair: its original signature fails because derivedPullback is imported only privately
through the restored chart. The original caller emits this error at line 151, followed
by a rank-instance error at line 177. It is unclaimed and is restored with no other edit.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

This replacement is made in both restored modules. All other Lean text is verbatim
from their quarantined modules. The node's Lean attachment,
statement and dependencies stay; its proof text now correctly names derivedPullback_spec.

## Users

The item is absent from lean/, so tools/downstream.py reports an unknown module. A direct
search over lean/ and quarantine/ finds exactly the caller below. The node parent remains
lem-sc-picard-single-rank-perfect-chart; no withdrawal or parent pruning is attempted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | N4 (this assignment) | Restore archived complete proof with corrected public import. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | quarantined; unclaimed | Restore with the identical one-line import correction; the original fails at line 151 against the restored chart. All existing signatures and proofs stay verbatim. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | quarantined; not edited | Sole caller of the restored Picard chart, at line 86. Unchanged tuple; no direct derivedPullback use or adaptation. |

## Status

landed 20261021T233749-L-858088 2026-10-21 (merge of deliver/N4/Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart)
