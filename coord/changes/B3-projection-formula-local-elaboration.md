# ProjectionFormula local elaboration repair

## Reason

The original module times out at 60 seconds, and its earlier A4 delivery was returned
for a 68-second global compile (coord/repair-notes/WeilConjectures.PoincareDuality.ProjectionFormula.json).
Share the monoidal and tensor-data instances locally, and keep the derived functors
and closed structures folded during elaboration. The repaired full module compiles in 41.2 seconds.
Every existing declaration attribute, signature, visibility, and definition body is unchanged.
Only boundedConstructibleExceptionalProjectionMorphism_natural_right receives a new proof.
No target text or mathematical construction changes.

## Old

The module began its public section directly with `universe u`, and used the generic
monoidal and tensor-data instance search. The naturality declaration ended `:= sorry`.
No local projectionMonoidal or projectionTensorData alias was present.

## New

```lean
noncomputable section

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

local instance projectionMonoidal (Z : Scheme.{u}) :
    MonoidalCategory (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :=
  Mod.derivedMonoidalCategory

local instance projectionTensorData (Z : Scheme.{u}) :
    MonoidalCategoryStruct (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :=
  (projectionMonoidal (Λ := Λ) Z).toMonoidalCategoryStruct

attribute [local instance 3000] projectionMonoidal projectionTensorData
```

The aliases refer to the original instance and its field, without changing their data.
The bounded naturality proof applies ObjectProperty.hom_ext, explicitly reduces the
restricted functors and tensor operations, then applies
exceptionalProjectionMorphismOfCompactification_natural_right to the underlying morphism.
No construction is replaced and no definition is hidden or made irreducible outside this module.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.PoincareDuality.ProjectionFormula | B3 | Local elaboration aliases and one completed proof. |
| TargetsCheck | unclaimed | Unchanged transitive importer; no adaptation. |
| WeilConjectures | unclaimed | Unchanged transitive importer; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | G3 | Unchanged transitive importer; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Same definitions and signatures; no adaptation. |

The downstream list is from tools/downstream.py with --uses and a source-occurrence check.
The aliases are local and definitionally the old instances; no consumer changes meaning.
There are no forced adaptations.

## Status

landed 20261017T125159-L-1106991 2026-10-17 (merge of deliver/B3/WeilConjectures.PoincareDuality.ProjectionFormula)
