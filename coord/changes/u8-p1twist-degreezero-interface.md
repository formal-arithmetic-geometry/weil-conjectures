# AlgebraicGeometry.Etale.p1DecompositionTwist

## Reason

Use the shared degree-zero construction `ordinaryFiniteDegreeZero` before shifting.
This is definitionally equal to the old `singleFunctor.obj` expression, but lets the
kernel compare the finite sheaf arguments before expanding the concrete single
functor. The ordinary finite line uses exactly the same interface. No mathematical
object, transport, hypothesis, signature, visibility or public import changes.
The direct private Kummer import records the construction dependency explicitly.

## Old

```lean
abbrev p1DecompositionTwist (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u}) (a b : ℤ) :
    DerivedCategoryModule A T :=
  ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A N T hA a))⟦b⟧
```

## New

```lean
abbrev p1DecompositionTwist (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u}) (a b : ℤ) :
    DerivedCategoryModule A T :=
  (ordinaryFiniteDegreeZero A T (Scheme.finiteEtaleTateSheaf A N T hA a))⟦b⟧
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.FiniteTwistDerivedEvaluationPullback` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | U8 | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Untwist` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.SpP1NormalizedFamilyCore` | unclaimed | definitionally identical object; no adaptation |

## Status

landed 20261024T191435-L-356888 2026-10-24 (merge of deliver/U8/Sheaf.AlgebraicGeometry.GeoP1Cohomology)
