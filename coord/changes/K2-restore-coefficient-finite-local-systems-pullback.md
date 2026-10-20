# CategoryTheory.coefficient_finite_local_systems_pullback

## Reason

Restore the module assigned by coord/rework.tsv after the cluster-restore quarantine.
The active source path is absent; the complete proved module is preserved at
quarantine/Sheaf/CategoryTheory/CoefficientFiniteLocalSystemsPullback.lean.
This delivery restores that archive verbatim, including its private constructions,
public import, theorem signature and complete proof. It does not retire the theorem.

## Old

The active module lean/Sheaf/CategoryTheory/CoefficientFiniteLocalSystemsPullback.lean
is absent. Its quarantined public theorem signature is:

```lean
theorem coefficient_finite_local_systems_pullback
    (F : Sheaf J (ModuleCat.{w} R))
    (hF : IsCoefficientModelLocallyConstantFinite J R F) :
    IsCoefficientModelLocallyConstantFinite K R
      ((Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{w} R) J K).obj F)
```

## New

Restore the complete archived module to its recorded active path. The signature above,
its section parameters, and all public imports are identical to the archive.
The source and DAG attachment remain unchanged. No definition is changed or weakened.

## Users

The downstream.py query reports an unknown module because the active path is absent.
A direct search of lean/Sheaf and quarantine/Sheaf finds the following sole consumer.
The parent DAG also retains this dependency in its proof step and proof_deps.
No consumer changes are required by this verbatim restoration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CoefficientFiniteLocalSystemsPullback | K2 | Restore proved module. |
| Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility | unclaimed, quarantined | Both existing applications retain the exact interface. |

The restored module compiles cleanly, and its theorem uses only propext,
Classical.choice and Quot.sound. An unchanged sandbox copy of the consumer was checked
against the restored module; the compiler stopped at its first import because
Sheaf.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules has no published
object file. Thus full consumer compilation awaits restoration of that separate
dependency. The consumer is not included in this delivery.
No target statement or definition used by a target is altered.

## Status

landed 20261020T221231-L-4161861 2026-10-20 (merge of deliver/K2/Sheaf.CategoryTheory.CoefficientFiniteLocalSystemsPullback)
