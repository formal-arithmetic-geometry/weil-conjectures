# moduleCup_sourceLax

## Reason

Name the canonical localization lax structure as an abbreviation so the polygon
can receive it explicitly, with a reflexive canonical-normalization equality.
This retains the exact construction of the original definition. The returned
version showed that this alone did not prevent the 60-second timeout (H10).
The H10 repair additionally shares the existing global pullback instances at the
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
The target module keeps the original local instance types and bodies and the
original comparison definition. The red-build repair gives the seven anonymous
instances explicit `moduleCupTarget...` names, avoiding the generated-name
collision with `GlobalTensorPullbackMonoidalNormalization` in non-module imports.
After those definitions, it activates the common instances for theorem elaboration:

```lean
attribute [local instance 2000] globalPullbackCommRing globalPullbackMonoidal
  globalPullbackSymmetric globalPullbackColimits globalPullbackPreadditive
  globalPullbackClosed globalPullbackFlatResolution
```

The new polygon uses the same local activation. Its pullback import is public
because the polygon hypothesis names the tensor-diagram declaration. The target
imports the pullback and polygon privately, preventing proof dependencies from
leaking into downstream importers. Private imports alone were insufficient for
the non-module batch probe: the unique local instance names repair that collision.
This changes instance expression sharing, not the tensor construction or any hypothesis or conclusion. No target
statement is weakened, and no definition obtains data from an unproved
existence theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ModuleCupKInjectiveTarget | XR9e6d7250028f1981 | Own proof shares pullback instances; locals uniquely named. |
| Sheaf.Paper.ModuleCupNaiveDerivedCompatibility | unclaimed | Unchanged source checked against overlay. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftLeft | unclaimed | Own local instance bodies are unchanged; no explicit use of a renamed target instance. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftRight | unclaimed | Own local instance bodies are unchanged; no explicit use of a renamed target instance. |
| Sheaf.Paper.ModuleCupDerivedClassComparison | unclaimed | Own local instance bodies are unchanged; no explicit use of a renamed target instance. |
| Sheaf.Paper.ModuleCupEqualDerivedMapsClass | Q3 | Own local instance bodies are unchanged; no explicit use of a renamed target instance. |
| Sheaf.Paper.ModuleCupRealizationEvaluation | unclaimed | Own local instance bodies are unchanged; no explicit use of a renamed target instance. |
| Sheaf.Paper.ModuleCupResolutionInvariance | unclaimed | Own local instance bodies are unchanged; no explicit use of a renamed target instance. |
The sourceLax declaration-use check lists the target and its direct compatibility
importer. The delivery preflight also lists the six modules above because its
source-level anonymous-instance keys match their own identically typed local
instances. Those modules do not refer to the renamed generated instance names;
their own tensor structures and mathematical statements remain unchanged. No
module outside the item and its polygon is adapted. The direct importer was
compiled unchanged against the repaired overlay. Final checks are in report.md.

## Status

landed 20261014T004117-L-2840312 2026-10-14 (merge of deliver/XR9e6d7250028f1981/Sheaf.Paper.ModuleCupKInjectiveTarget)

Repairs the returned landing 20261013T234503-L-2160123 (A2), including its
non-module batch-probe import failure. Final independent checks are in report.md.
