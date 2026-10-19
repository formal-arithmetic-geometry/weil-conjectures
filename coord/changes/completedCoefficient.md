# completedCoefficient

## Reason

The coefficient object was an `abbrev`, so elaborating the pullback comparison repeatedly
expanded the full monoidal coefficient construction. This made the target proof exceed the
single-file compiler timeout. A regular definition preserves the same inferred type and
body while giving elaboration a stable reduction boundary. There is no mathematical
change: the old and new objects are definitionally equal, including their ring structures.
No target signature changes. Since this definition lies below the targets, the definition
change is submitted for independent statement review again as required by the brief.

## Old

```lean
noncomputable abbrev completedCoefficient (X : Scheme.{u})
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}) :=
  coefficientRing X
    (Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R))
```

## New

```lean
noncomputable def completedCoefficient (X : Scheme.{u})
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}) :=
  coefficientRing X
    (Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R))
```

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.CompletedCondensedCoefficients` | N3 | All statements retained; module compiles in 34.7 s. |
| `Sheaf.SixFunctors.IntegralModelsGenerators` | T3 | Compiles unchanged; its uses remain definitionally well typed. |

## Status

landed 20261019T231250-L-567498 2026-10-19 (merge of deliver/N3/Sheaf.Paper.CompletedCondensedCoefficients)
