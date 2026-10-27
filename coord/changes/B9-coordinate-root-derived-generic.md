# AlgebraicGeometry.ProEtale.AffineZeroPurity.coordinateRootDerived and coordinateRealizeRootBoundary

## Reason

The original definition expands the exact derived comparison and shift functors
while Lean checks the composite. A profiled compile passes the new support proof
in under a second and reaches `coordinateRootDerived` and
`coordinateRealizeRootBoundary`, then times out at the fixed 60-second limit.
The trace shows repeated comparison of localization-defined derived functors
with the same functors composed with shifts.

Express the same shifted comparison through a local helper for an arbitrary
functor commuting with shifts. The helper is instantiated at the original derived
site comparison. Its body is exactly the original shift comparison followed by
the shift of the single-complex comparison and the sheaf isomorphism. No new
choice, hypothesis, public declaration, or mathematical construction is added.
The original binders are kept; the result is now explicitly annotated with the
definitionally identical isomorphism type (functor composition object projections reduce to the stated
functor applications). The helper unfolds to the original body. A diagnostic compile of the prefix
through this definition, including both completed support and root uniqueness
proofs, passed in 16.8 seconds. Explicit endpoint annotation avoids inferring
endpoints by expanding the localization-defined comparison.

## Old

```lean
def coordinateRootDerived (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] (X : Scheme.{u})
    {L : Sheaf X.smallEtaleTopology V} {M : Sheaf (Scheme.ProEt.topology X) V}
    (e : (comparisonUpperStar V X).obj L ≅ M) :=
  (((comparisonUpperStar V X).mapDerivedCategory).commShiftIso (2 : ℤ)).app
      ((DerivedCategory.singleFunctor _ 0).obj L) ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      (((comparisonUpperStar V X).mapDerivedCategorySingleFunctor 0).app L
        ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e)
```

## New

```lean
def coordinateRootDerived (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] (X : Scheme.{u})
    {L : Sheaf X.smallEtaleTopology V} {M : Sheaf (Scheme.ProEt.topology X) V}
    (e : (comparisonUpperStar V X).obj L ≅ M) :
    (comparisonUpperStar V X).mapDerivedCategory.obj
      (((DerivedCategory.singleFunctor _ 0).obj L)⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj M)⟦(2 : ℤ)⟧ :=
  let realize {C D S T : Type (max (u + 1) v)} [Category.{u + 1} C]
      [Category.{u + 1} D] [Category.{u + 1} S] [Category.{u + 1} T]
      [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ]
      (s : S ⥤ C) (t : T ⥤ D) (G : S ⥤ T) (ι : s ⋙ F ≅ G ⋙ t)
      {L : S} {M : T} (e : G.obj L ≅ M) :
      F.obj ((s.obj L)⟦(2 : ℤ)⟧) ≅ (t.obj M)⟦(2 : ℤ)⟧ :=
    (F.commShiftIso (2 : ℤ)).app (s.obj L) ≪≫
      (shiftFunctor _ (2 : ℤ)).mapIso (ι.app L ≪≫ t.mapIso e)
  realize (comparisonUpperStar V X).mapDerivedCategory
    (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
    (comparisonUpperStar V X)
    ((comparisonUpperStar V X).mapDerivedCategorySingleFunctor 0) e
```

The same technique is required for `coordinateRealizeRootBoundary`: construct
its original composite over arbitrary categories, functors, shifts and a specified
single-complex comparison, then specialize to the exact site comparison. The
helper's root arrows are exactly the defining body of `coordinateRootDerived`;
it composes the same `realizeBoundary`, `coordinateArrowComparison` and
`coordinateIsoThrough` operations in the same order. Its result annotation states
the original inferred endpoints explicitly. This is a definitionally identical
construction, not a new realization or orientation. The diagnostic prefix through
both revised definitions compiled in 25.8 seconds; its slowest kernel check was
16.3 seconds.

### Old coordinateRealizeRootBoundary

```lean
def coordinateRealizeRootBoundary (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (L L' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    {J : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)}
    (α : CategoryTheory.Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj M) L 2)
    (e : (comparisonUpperStar (ModuleCat.{u + 1} A) X).obj L ≅ J)
    (e' : (comparisonUpperStar (ModuleCat.{u + 1} A) X).obj L' ≅ J) :=
  coordinateArrowComparison (realizeBoundary A i M L α)
    (coordinateIsoThrough (coordinateRootDerived (ModuleCat.{u + 1} A) X e)
      (coordinateRootDerived (ModuleCat.{u + 1} A) X e'))
```

### New coordinateRealizeRootBoundary

```lean
def coordinateRealizeRootBoundary (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (L L' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    {J : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)}
    (α : CategoryTheory.Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj M) L 2)
    (e : (comparisonUpperStar (ModuleCat.{u + 1} A) X).obj L ≅ J)
    (e' : (comparisonUpperStar (ModuleCat.{u + 1} A) X).obj L' ≅ J) :
    (DerivedCategory.singleFunctor _ 0).obj
      ((lowerStar (ModuleCat.{u + 1} A) i).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj M)) ⟶
      (VectorIntegrationSite.comparison A X).obj
        (((DerivedCategory.singleFunctor _ 0).obj L')⟦(2 : ℤ)⟧) :=
  let compare {C D S T : Type (u + 2)} [Category.{u + 1} C]
      [Category.{u + 1} D] [Category.{u + 1} S] [Category.{u + 1} T]
      [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ]
      (s : S ⥤ C) (t : T ⥤ D) (G : S ⥤ T) (ι : s ⋙ F ≅ G ⋙ t)
      {K : D} {L L' : S} {J : T}
      (f : K ⟶ F.obj ((s.obj L)⟦(2 : ℤ)⟧))
      (e : G.obj L ≅ J) (e' : G.obj L' ≅ J) :
      K ⟶ F.obj ((s.obj L')⟦(2 : ℤ)⟧) :=
    let root {L : S} (e : G.obj L ≅ J) :
        F.obj ((s.obj L)⟦(2 : ℤ)⟧) ≅ (t.obj J)⟦(2 : ℤ)⟧ :=
      (F.commShiftIso (2 : ℤ)).app (s.obj L) ≪≫
        (shiftFunctor _ (2 : ℤ)).mapIso (ι.app L ≪≫ t.mapIso e)
    coordinateArrowComparison f (coordinateIsoThrough (root e) (root e'))
  compare (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
    (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
    (comparisonUpperStar (ModuleCat.{u + 1} A) X)
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategorySingleFunctor 0)
    (realizeBoundary A i M L α) e e'
```

## Users

`tools/downstream.py Sheaf.Paper.CoordinateProductPresentations --uses
coordinateRootDerived` and the same command with `--uses coordinateRealizeRootBoundary` report
the single downstream module below and only
internal textual uses of the changed definition. The consumer does not mention
or unfold either changed definition; its public arrow constructions retain exactly
the same endpoints and maps. No consumer source change is required. No target
meaning or unit route changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CoordinateProductPresentations | B9 | Same shifted comparison, composed generically before specialization. |
| Sheaf.Paper.CoordinateSectionProductRecursion | Y8 | Same public API and definitions by reduction; no adaptation. |

The complete final module, with all profiling options removed, compiled cleanly
through `lcompile.py` in 25.3 seconds (exit code 0, no warnings or errors).

## Status

landed 20261025T180454-L-3993997 2026-10-25 (merge of deliver/B9/Sheaf.Paper.CoordinateProductPresentations)
