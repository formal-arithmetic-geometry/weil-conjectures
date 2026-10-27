# Explicit geometric arguments in ConstantPurityFrobenius.systems

## Reason

The original implicit final application searched through large coefficient-category
constructions during elaboration. The complete item exceeded 60 seconds. Passing
its existing geometric proofs directly lets this application respect transparency;
the profiled item then compiled in 49.1 seconds.

## Old

After local instances for each geometric property:

```lean
  ConstructibleExceptionalCoefficients.System l Ω D hl
    (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber (point D)).left)
    (f := FrobeniusExchange.fiberMap D (pointMap D X₀))
```

## New

The final application supplies all those same proofs as explicit arguments:

```lean
  @ConstructibleExceptionalCoefficients.System l inferInstance Ω
    inferInstance inferInstance inferInstance D hl
    (D.geometricFiber X₀).left (D.geometricFiber (point D)).left
    (FrobeniusExchange.fiberMap D (pointMap D X₀)) inferInstance inferInstance
    (FrobeniusExchange.fiber_finiteType D X₀).1
    (FrobeniusExchange.fiber_finiteType D X₀).2
    (FrobeniusExchange.fiber_finiteType D (point D)).1
    (FrobeniusExchange.fiber_finiteType D (point D)).2
    (zlFiberMap_isOver D (pointMap D X₀))
    (FrobeniusExchange.fiberMap_properties D (pointMap D X₀)).1
    (FrobeniusExchange.fiberMap_properties D (pointMap D X₀)).2.1
    (FrobeniusExchange.fiberMap_properties D (pointMap D X₀)).2.2
```

Its instance proofs are proof irrelevant. The resulting type, all geometric data,
and every public signature remain definitionally equal. No definition is made
irreducible. The existing transparency options for this definition are changed to
true. An unused open of CategoryTheory.Endofunctor is also removed to prevent
repeated failed resolution of the field Algebra name.

## Users

Sheaf.Paper.ConstantPurityFrobeniusSquare is held by B3. There are no current Lean
direct importers of that module. The target-facing Square definition and theorem
statement are unchanged. The item's DAG attachment records the implementation
change without changing its mathematical statement.

## Status

landed 20261026T235831-L-1458993 2026-10-26 (merge of deliver/B3/Sheaf.Paper.ConstantPurityFrobeniusSquare)
