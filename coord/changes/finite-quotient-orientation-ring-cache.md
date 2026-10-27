# AlgebraicGeometry.ProEtale.SpFiniteOrientation.quotientCoefficientCommRing

## Reason

After proving the quotient comparison, checking its concrete coefficient structures
and exporting its premise indices exceeded the 60-second limit. Moving the generic
argument to its own module alone did not fix the cost; the concrete specialization
still took 75 seconds. A named direct cache of the existing commutative-ring
structure, together with that generic proof, brought the diagnostic compile down to
38.6 seconds, including its profiling and structure-inspection commands. The cache
matches explicit prime and extension parameters, unlike the existing cache whose
parameters are projections of a `PurityFiniteSetting`. No check, index, heartbeat
limit or compile limit is disabled.

## Old

There was no named structure with these explicit parameters. In the unchanged
quotient-orientation signature the concrete coefficient type is:

```lean
ULift.{u + 1} (SpTowerShriek.R l E n)
```

Typeclass synthesis supplied its ordinary lifted quotient-ring structure directly.
Every existing declaration's statement text and every existing definition body
is retained verbatim.

## New

```lean
@[instance_reducible]
def quotientCoefficientCommRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    CommRing (ULift.{u + 1} (SpTowerShriek.R l E n)) := inferInstance

section QuotientOrientation
attribute [local instance] quotientCoefficientCommRing
```

The section ends immediately after `finite_orientation_reduction`. The cache's
body is ordinary structure synthesis before its own registration. It contains
no hole or choice of mathematical data. Its operations and laws are definitionally
the original ones. It exports no additional global instance. The existing
`towerCoefficientCommRing` cache and all other declaration bodies remain unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteOrientationReduction | S7 | The quotient theorem locally reuses the named dictionary. Its statement text and actual coefficient map stay unchanged. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed | Direct importer; uses only `unit_tower_mem`. Checked against the cache without adaptation. |
| Sheaf.Paper.CompositeProjectionCoefficients | unclaimed | Direct importer; uses only `unit_tower_mem`. Checked against the cache without adaptation. |

The direct-import search and `tools/downstream.py --uses finite_orientation_reduction`
found these two importers and no external use of the quotient-orientation theorem.
Both direct importers compiled cleanly against the final cache through `lcompile.py`.
The unchanged importer copies have been removed from the delivery sandbox.
No target statement changes mathematically or textually.

## Status

landed 20261027T034742-L-3681791 2026-10-27 (merge of deliver/S7/Sheaf.Paper.FiniteOrientationReduction)
