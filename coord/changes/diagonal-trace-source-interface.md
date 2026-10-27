# AlgebraicGeometry.ProEtale.DiagonalTrace.SupportedSource and companion definitions

## Reason

Extract the existing seven model/source declarations to `Sheaf.Paper.DiagonalTraceSources` so the separate system-construction lemma can use them without importing the theorem it helps prove. The item publicly imports that interface. Definitions, signatures, namespaces, visibility and mathematical meaning are byte-identical. No source-library file changes.

## Old

In `lean/Sheaf/Paper/DiagonalTowerTrace.lean`:

```lean
/-- The specified projective-line model of the first product projection.
Source: blueprint trace clause 1 (blueprint: det-prop-diagonal-tower-trace). -/
def diagonalTraceFirstModel (Y : Scheme.{u}) :
    diagonalSurface Y ≅ ProjectiveLine (ProjectiveLine Y) :=
  ((ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2))
    (ProjectiveLine Y ↘ Y)).flip.isoPullback).symm

/-- The second projective-line model uses the canonical factor interchange.
Source: blueprint trace clause 1 (blueprint: det-prop-diagonal-tower-trace). -/
def diagonalTraceSecondModel (Y : Scheme.{u}) :
    diagonalSurface Y ≅ ProjectiveLine (ProjectiveLine Y) :=
  pullbackSymmetry (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) ≪≫
    diagonalTraceFirstModel Y

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- Normalized source data for an ordinary direct image and its right derived functor.
The predicate fixes the ordinary comparison; the last field asserts its acyclicity.
Source: blueprint trace proof step 9 (blueprint: det-prop-diagonal-tower-trace). -/
structure NormalizedSource
    {A : Type a} {B : Type a} [Category.{va} A] [Category.{va} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] (R : DiagonalRightDerived F) (M : A) (N : B)
    (P : Prop) (normalizes : (N ≅ F.obj M) → P → Prop) where
  over_eq : P
  iso : N ≅ F.obj M
  normalization : normalizes iso over_eq
  acyclic : IsIso (diagonalTraceRightSingle F R M)

/-- The canonical map from a normalized coefficient source to its derived direct image.
Source: blueprint trace proof step 9 (blueprint: det-prop-diagonal-tower-trace). -/
def NormalizedSource.hom
    {A : Type a} {B : Type a} [Category.{va} A] [Category.{va} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    {F : A ⥤ B} [F.Additive] {R : DiagonalRightDerived F} {M : A} {N : B}
    {P : Prop} {normalizes : (N ≅ F.obj M) → P → Prop}
    (s : NormalizedSource F R M N P normalizes) :
    (DerivedCategory.singleFunctor B 0).obj N ⟶
      R.R.obj ((DerivedCategory.singleFunctor A 0).obj M) :=
  (DerivedCategory.singleFunctor B 0).map s.iso.hom ≫ diagonalTraceRightSingle F R M

/-- The integration identity for a specified source comparison and trace.
Source: blueprint trace clause 2 (blueprint: det-prop-diagonal-tower-trace). -/
def IsIntegration
    {C : Type a} {D : Type b} [Category.{va} C] [Category.{vb} D]
    (R : C ⥤ D) {M N : C} {K : D} (a : K ⟶ R.obj M) (t : R.obj N ⟶ K)
    (δ : M ⟶ N) : Prop := a ≫ R.map δ ≫ t = 𝟙 K

/-- The ordinary supported-source identification is normalized by actual composition
of additive direct images, the equality f Delta = id, and the identity direct image.
Source: blueprint trace proof step 9 (blueprint: det-prop-diagonal-tower-trace). -/
def supportedSourceNormalization (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (i : SheafOfModules.unit
      (Scheme.purTwistRing (ProjectiveLine Y) (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)) ≅
      (diagonalTracePush l f).obj (diagonalCompletedSource l Y))
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) : Prop :=
  HEq ((diagonalCompletedRestriction l (ProjectiveLine Y) ⋙
      diagonalForget l (ProjectiveLine Y)).map i.inv)
    (((lowerStarComp AddCommGrpCat.{u + 1} (diagonalImmersion Y) f) ≪≫
      lowerStarCongr AddCommGrpCat.{u + 1} h ≪≫
      lowerStarId AddCommGrpCat.{u + 1} (ProjectiveLine Y)).hom.app
        ((diagonalCompletedRestriction l (ProjectiveLine Y) ⋙
          diagonalForget l (ProjectiveLine Y)).obj
            (SheafOfModules.unit (Scheme.purTwistRing (ProjectiveLine Y)
              (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)))))

/-- The source identification Rf_* Delta_* Z_l = Z_l uses the specified ordinary
composition map and the universal derived unit, which is invertible on this source.
Source: blueprint trace clause 2 and proof step 9
(blueprint: det-prop-diagonal-tower-trace). -/
abbrev SupportedSource (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalCompleted l (ProjectiveLine Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted l (diagonalSurface Y))]
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    [(diagonalTracePush l f).Additive]
    (R : DiagonalRightDerived (diagonalTracePush l f)) :=
  NormalizedSource (diagonalTracePush l f) R (diagonalCompletedSource l Y)
    (SheafOfModules.unit (Scheme.purTwistRing (ProjectiveLine Y)
      (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)))
    (diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y))
    (supportedSourceNormalization l Y f)

end AlgebraicGeometry.ProEtale.DiagonalTrace
```

## New

The identical declaration block above is in `lean/Sheaf/Paper/DiagonalTraceSources.lean`; the original module re-exports it with `public import Sheaf.Paper.DiagonalTraceSources`. The new interface publicly imports the same four original statement dependencies, preserving their visibility. The original theorem signature remains verbatim. The normalized-source node attachment moves to this interface; the new source-definition node records the five other moved declarations. Adding this owner to statement dependencies records the extraction only.

## Users

`tools/downstream.py` lists the following 18 downstream modules. Direct textual users are DiagonalCoefficientCategory (NormalizedSource) and DiagonalCoefficientReference (first projection model). Neither requires adaptation: importing the original module exports the exact same declarations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | unchanged; original public names re-exported |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | unchanged; original public names re-exported |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | unchanged; original public names re-exported |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | unchanged; original public names re-exported |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | unchanged; original public names re-exported |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | unchanged; original public names re-exported |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | unchanged; original public names re-exported |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | unchanged; original public names re-exported |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | unchanged; original public names re-exported |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | unchanged; original public names re-exported |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | unchanged; original public names re-exported |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | unchanged; original public names re-exported |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | unchanged; original public names re-exported |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | unchanged; original public names re-exported |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | unchanged; original public names re-exported |
| Sheaf.Paper.DiagonalTowerCoefficients | E5 | unchanged; original public names re-exported |
| Sheaf.Paper.ProjectiveDiagonalPullback | unclaimed | unchanged; original public names re-exported |
| Sheaf.Paper.RationalTatePullback | unclaimed | unchanged; original public names re-exported |
| Sheaf.Paper.DiagonalTowerTrace | E7 | proof replaced; interface re-exported |

The Challenge targets retain their signatures and the meaning of every referenced definition. No consumer statement becomes stronger, weaker or different. There are no forced adaptations.

## Status

landed 20261023T231004-L-3527995 2026-10-23 (merge of deliver/E7/Sheaf.Paper.DiagonalTowerTrace)
