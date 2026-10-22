# AlgebraicGeometry.Etale.isIso_etaleStalkSpecialization_of_proper_locallyAcyclic

## Reason

Restore the assigned quarantined module from
quarantine/Sheaf/AlgebraicGeometry/ProperLocallyAcyclicSpecialization.lean,
listed in coord/rework.tsv. The archived proof is complete and has zero holes.
Compiling that archive unchanged reports at line 300:

```text
Unknown identifier `rightDerivedLowerStarPlus`
A public declaration `rightDerivedLowerStarPlus` exists but is imported privately;
consider adding the public UpperLowerStarCoherence import.
```

Its public theorem statement needs the derived-direct-image definition. Add the
explicit public import of its defining source module. This is the same visibility
repair described in the landed A3-module-specialization-generic-restriction record;
the item remains absent from lean/ and its quarantine archive still lacks that import.
The restored file compiles cleanly in 23.2 seconds with this repair.

All archived declarations, signatures, proof bodies, attributes and docstrings are
preserved verbatim. No mathematical object, hypothesis, conclusion, target meaning
or source-library file changes. The existing DAG node and its Lean attachment remain
unchanged, as does its five-step proof route.

## Old

The live item path is absent. The quarantine archive has these public imports:

```lean
public import Sheaf.AlgebraicGeometry.EtaleStalkSpecialization
public import Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
```

## New

Restore the entire archive unchanged except for adding:

```lean
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
```

This supplies the existing `rightDerivedLowerStarPlus` in the public statement.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization | A3 | Restore the complete proof and repair public visibility. |
| Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization | unclaimed, quarantined | Sole archived direct consumer and DAG parent; calls the unchanged theorem at line 138; no adaptation caused by this import addition. |

`tools/downstream.py --allow-missing --uses` finds zero live downstream modules.
Searching lean/ and quarantine/ finds only the archived direct consumer listed above.
The parent remains in the DAG and is not pruned. No existing import or declaration
is removed, and no consumer can lose an exported name or instance from this addition.

## Status

landed 20261022T021022-L-161802 2026-10-22 (merge of deliver/A3/Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization)
