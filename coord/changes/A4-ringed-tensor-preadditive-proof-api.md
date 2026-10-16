# SheafOfModules.ringedTensorPreadditive

## Reason

The full-file profiler identified repeated expansion of this proof-valued abbreviation
through tensorClosed and its large closure construction. Replace the abbreviation by
a theorem with exactly the same proposition. The second reading proves its four laws
directly from the tensorLeft and tensorRight additive instances, avoiding expansion of
the larger tensorClosed conjunction. MonoidalPreadditive is a proposition,
so proof irrelevance identifies the old and new values. No computational data or target
meaning changes. The same proof API is available to local-instance applications, without
expanding its proof during type checking. The full item file compiled in 53.4 seconds,
within the unchanged single-file limit.

## Old

```lean
noncomputable abbrev ringedTensorPreadditive :
    @MonoidalPreadditive (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) _ _ (monoidalCategory R) :=
  Classical.choice (tensorClosed R).1
```

## New

```lean
theorem ringedTensorPreadditive :
    @MonoidalPreadditive (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) _ _ (monoidalCategory R) :=
  by
    let := monoidalCategory R
    exact
      { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
        zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
        whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
        add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
```

## Users

A repository-wide declaration-name search finds these two users. Neither relies on
unfolding this proof to compute data. No module outside the item needs an adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingedTopoiCanonicalTensorPullback | A4 | same local-instance proposition |
| Sheaf.Paper.ProjectionFormulaArrows | unclaimed | same local-instance proposition |

The optional single-file check of the unchanged ProjectionFormulaArrows source
against this overlay reached the 60-second limit without reporting a compiler error.
The same unchanged source compiled against the baseline (61.0 seconds elapsed including
queue time). This does not establish a forced source adaptation; no consumer source
was changed. The independent reader checked an unchanged scratch copy of this consumer against
the delivered overlay: it compiled with no errors or warnings (60.5 seconds including
queue time). The item itself compiled cleanly in 50.0 seconds before the required dry run.

## Status

landed 20261016T011142-L-263526 2026-10-16 (merge of deliver/A4/Sheaf.Paper.RingedTopoiCanonicalTensorPullback)
