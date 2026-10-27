# geoP1TwistedMap, geoP1UnitExchange, geoP1TwistExchange

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
def geoP1TwistedMap (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    (geoP1Twist A N hA S 1 2 ⊞ geoP1Unit A S) ⟶
      (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
        (geoP1Twist A N hA (ProjectiveLine S) 1 2) :=
  geoP1SumComparison A S _ _ ≫
    (geoP1Comparison A S).map
      (Etale.projectiveLineTraceDatum N hN A hA S hS).decomposition.hom ≫
    geoP1PushComparison A (ProjectiveLine S ↘ S) _
```

```lean
def geoP1UnitExchange (A : Type (u + 1)) [CommRing A]
    {S' S : Scheme.{u}} (g : S' ⟶ S) :
    (geoP1Pullback A g).obj
        ((geoP1Pushforward A (ProjectiveLine S ↘ S)).obj (geoP1Unit A (ProjectiveLine S))) ⟶
      (geoP1Pushforward A (ProjectiveLine S' ↘ S')).obj (geoP1Unit A (ProjectiveLine S')) :=
  geoP1Exchange A g _ ≫ (geoP1Pushforward A (ProjectiveLine S' ↘ S')).map
    (geoP1UnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom
```

```lean
def geoP1TwistExchange (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S' S : Scheme.{u}} (g : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) :
    (geoP1Pullback A g).obj ((geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
      (geoP1Twist A N hA (ProjectiveLine S) 1 2)) ⟶
      (geoP1Pushforward A (ProjectiveLine S' ↘ S')).obj
        (geoP1Twist A N hA (ProjectiveLine S') 1 2) :=
  geoP1Exchange A g _ ≫ (geoP1Pushforward A (ProjectiveLine S' ↘ S')).map
    (geoP1TwistPullback A N hN hA (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)
      ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
        hS.map (ProjectiveLine S ↘ S).appTop.hom) 1 2).hom
```

## New

```lean
def geoP1TwistedMap (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    (geoP1Twist A N hA S 1 2 ⊞ geoP1Unit A S) ⟶
      (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
        (geoP1Twist A N hA (ProjectiveLine S) 1 2) :=
  geoP1SumComparison A S _ _ ≫
    (geoP1Comparison A S).map
      (Etale.projectiveLineTraceDatum N hN A hA S hS).decomposition.hom ≫
    geoP1PushComparison A (ProjectiveLine S ↘ S)
      ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
```

```lean
def geoP1UnitExchange (A : Type (u + 1)) [CommRing A]
    {S' S : Scheme.{u}} (g : S' ⟶ S) :
    (geoP1Pullback A g).obj
        ((geoP1Pushforward A (ProjectiveLine S ↘ S)).obj (geoP1Unit A (ProjectiveLine S))) ⟶
      (geoP1Pushforward A (ProjectiveLine S' ↘ S')).obj (geoP1Unit A (ProjectiveLine S')) :=
  geoP1Exchange A g _ ≫ (geoP1Pushforward A (ProjectiveLine S' ↘ S')).map
    (geoP1UnitPullback A
      (X := ProjectiveLine S') (Y := ProjectiveLine S)
      (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom
```

```lean
def geoP1TwistExchange (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S' S : Scheme.{u}} (g : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) :
    (geoP1Pullback A g).obj ((geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
      (geoP1Twist A N hA (ProjectiveLine S) 1 2)) ⟶
      (geoP1Pushforward A (ProjectiveLine S' ↘ S')).obj
        (geoP1Twist A N hA (ProjectiveLine S') 1 2) :=
  geoP1Exchange A g _ ≫ (geoP1Pushforward A (ProjectiveLine S' ↘ S')).map
    (geoP1TwistPullback A N hN hA
      (X := ProjectiveLine S') (Y := ProjectiveLine S) (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)
      ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
        hS.map (ProjectiveLine S ↘ S).appTop.hom) 1 2).hom
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | U8 | explicit arguments only; no mathematical change |
| `Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem` | unclaimed | definitionally identical interface; no adaptation required |
| `Sheaf.Paper.DiagonalCoefficientFiniteDiagonal` | unclaimed | definitionally identical interface; no adaptation required |

## Status

landed 20261024T191435-L-356888 2026-10-24 (merge of deliver/U8/Sheaf.AlgebraicGeometry.GeoP1Cohomology)
