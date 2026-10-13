# moduleCup_sourceLax

## Reason

Name the canonical localization lax structure as an abbreviation so the polygon
can receive it explicitly, with a reflexive canonical-normalization equality.
This retains the exact construction of the original definition. The returned
version showed that this alone did not prevent the 60-second timeout (H10).
The repair additionally shares the existing global pullback instances at the
theorem boundary. Their definitions are the same monoidal, symmetric, closed,
ring and resolution data as the existing local declarations.

## Old

```lean
@[instance_reducible]
def moduleCup_sourceLax :
    (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).LaxMonoidal :=
  inferInstance
```

## New

```lean
abbrev moduleCup_sourceLax :
    (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).LaxMonoidal :=
  inferInstance
```

The name, binders, universe, type, visibility and definition data are unchanged.
The target module keeps the original local instances and definitions. After
those definitions, it activates the common instances for theorem elaboration:

```lean
attribute [local instance 2000] globalPullbackCommRing globalPullbackMonoidal
  globalPullbackSymmetric globalPullbackColimits globalPullbackPreadditive
  globalPullbackClosed globalPullbackFlatResolution
```

The new polygon uses the same local activation. The target's import of
`Sheaf.Paper.ModuleCupGlobalTensorPullback` is public because its theorem's
elaborated type uses those existing constants. This changes instance expression
sharing, not the tensor construction or any hypothesis or conclusion. No target
statement is weakened, and no definition obtains data from an unproved
existence theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ModuleCupKInjectiveTarget | A2 | Own proof shares pullback instances. |
| Sheaf.Paper.ModuleCupNaiveDerivedCompatibility | unclaimed | Unchanged source checked against overlay. |

The fresh downstream declaration-use check lists precisely these two users.
No module outside the item and its new polygon is adapted. The report records
final compilation and dry-run results for this repair.

## Status

landed 20261013T234503-L-2160123 2026-10-13 (merge of deliver/A2/Sheaf.Paper.ModuleCupKInjectiveTarget)
