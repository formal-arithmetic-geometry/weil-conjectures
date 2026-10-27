# OrdinaryFiniteP1BaseChange

## Reason

Avoid expensive kernel conversion between inferred projective-space endpoints and the
`ProjectiveLine` abbreviation. Supply those endpoints explicitly. The twisted map also
supplies its shifted ordinary finite-line argument explicitly. Every change is
definitionally equal to the original; hypotheses, mathematical maps, visibility,
attributes and public imports are preserved. No definition data comes from a new
unproved existence statement. These are performance repairs needed for the comparison
proof to compile within the existing limit.

## Old

```lean
def OrdinaryFiniteP1BaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
      OrdinaryFiniteP1Datum A N hA t S hS) : Prop :=
  ∀ {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S]
    (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤))),
    ((ordinaryFinitePullback A f).map
        (d S hS).decomposition.hom ≫
      ordinaryFiniteP1Exchange A f ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
        (ordinaryFiniteShiftedLinePullback A N hA t
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) f) (d S hS).invertible_on_projectiveLine).hom =
    ordinaryFiniteP1DecompositionSourceMap A N hA t f hS ≫
      (d S' hS').decomposition.hom) ∧
    ((ordinaryFinitePullback A f).map (d S hS).trace ≫
        (ordinaryFiniteUnitPullback A f).hom =
      ordinaryFiniteP1Exchange A f ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
              (d S hS).invertible_on_projectiveLine).hom ≫ (d S' hS').trace) ∧
    ∀ K : DerivedCategoryModule A S,
      (ordinaryFinitePullback A f).map
          ((d S hS).adjunction.counit.app K) =
        ordinaryFiniteP1Exchange A f ((ordinaryFiniteP1Right A N hA S).obj K) ≫
          (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
            (ordinaryFiniteP1RightBaseChange A N hA t f
              (d S hS).invertible_on_projectiveLine K).hom ≫
          (d S' hS').adjunction.counit.app
            ((ordinaryFinitePullback A f).obj K)
```

## New

```lean
def OrdinaryFiniteP1BaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
      OrdinaryFiniteP1Datum A N hA t S hS) : Prop :=
  ∀ {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S]
    (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤))),
    ((ordinaryFinitePullback A f).map
        (d S hS).decomposition.hom ≫
      ordinaryFiniteP1Exchange A f ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
        (ordinaryFiniteShiftedLinePullback A N hA t
          (X := ProjectiveLine S') (Y := ProjectiveLine S)
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) f) (d S hS).invertible_on_projectiveLine).hom =
    ordinaryFiniteP1DecompositionSourceMap A N hA t f hS ≫
      (d S' hS').decomposition.hom) ∧
    ((ordinaryFinitePullback A f).map (d S hS).trace ≫
        (ordinaryFiniteUnitPullback A f).hom =
      ordinaryFiniteP1Exchange A f ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (X := ProjectiveLine S') (Y := ProjectiveLine S)
            (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
              (d S hS).invertible_on_projectiveLine).hom ≫ (d S' hS').trace) ∧
    ∀ K : DerivedCategoryModule A S,
      (ordinaryFinitePullback A f).map
          ((d S hS).adjunction.counit.app K) =
        ordinaryFiniteP1Exchange A f ((ordinaryFiniteP1Right A N hA S).obj K) ≫
          (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
            (ordinaryFiniteP1RightBaseChange A N hA t f
              (d S hS).invertible_on_projectiveLine K).hom ≫
          (d S' hS').adjunction.counit.app
            ((ordinaryFinitePullback A f).obj K)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace` | unclaimed | definitionally identical interface; no adaptation required |
| `Sheaf.AlgebraicGeometry.AffineTraceLineCounitBaseChange` | unclaimed | definitionally identical interface; no adaptation required |
| `Sheaf.AlgebraicGeometry.AffineTraceTowerCounitBaseChange` | unclaimed | definitionally identical interface; no adaptation required |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction` | unclaimed | definitionally identical interface; no adaptation required |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data` | unclaimed | explicit arguments only; no mathematical change |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DatumUniqueness` | unclaimed | definitionally identical interface; no adaptation required |
| `Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility` | unclaimed | definitionally identical interface; no adaptation required |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | U8 | proof completed here |

## Status

landed 20261024T191435-L-356888 2026-10-24 (merge of deliver/U8/Sheaf.AlgebraicGeometry.GeoP1Cohomology)
