# AlgebraicGeometry.Etale.ordinaryFiniteP1DiagonalSupportedMap

## Reason

Repeated realization of the supported composite caused expensive conversions of
inferred derived-category and Ext instances. Record its actual Ext group,
exact-derived realization and complete supported arrow on the existing named
objects. The projected map retains the original alpha-then-realization composite, using
the named realization. Unfolding that wrapper gives its old value.
ordinaryFiniteSupportedArrow_pushforward supplies the factoring equation used
inside the component proof, by map_comp and associativity.
Every datum is a literal construction; no witness or proof is postponed.

Existing public imports and attributes are preserved. The new coefficient-record module is
additionally imported publicly because the new chart-transport definition uses its
recorded adjunction. Published ordinary finite arrow and supported-unit definitions
are restored verbatim, and their proved equality interfaces are used only in the
component proof. The supported-map and
component-theorem kappa binders use the definitionally equal named Ext group;
all other binders and conclusions are unchanged. The supported-map value is
definitionally the same original composite after unfolding the realization wrapper.
Review of all targets using this definition is reopened for this equality and
the identical interpretation of the named Ext group. No adopted source module
or target declaration is edited.

## Old

```lean
@[irreducible]
def ordinaryFiniteP1DiagonalSupportedMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) (a : Bool)
    (κ : Ext
      (C := Sheaf
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).smallEtaleTopology
        (ModuleCat.{u + 1} A))
      ((lowerStar (ModuleCat.{u + 1} A) (Z := ProjectiveLine S)
        (Y := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
        (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2) :
    ordinaryFiniteUnit A (ProjectiveLine S) ⟶ ordinaryFiniteP1DiagonalTarget A N hA S a :=
  projectiveLineDiagonalAlpha A S a ≫
    (ordinaryFinitePushforward A
      (X := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) (Y := ProjectiveLine S)
      (projectiveLineDiagonalProjection S a)).map
        (X := (ordinaryFinitePushforward A (X := ProjectiveLine S)
          (Y := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
          (pullback.diagonal (ProjectiveLine S ↘ S))).obj
            (ordinaryFiniteUnit A (ProjectiveLine S)))
        (Y := (ordinaryFiniteLine A N hA
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)
        (supportedExactDerivedMap
          (lowerStar (ModuleCat.{u + 1} A) (Z := ProjectiveLine S)
            (Y := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
            (pullback.diagonal (ProjectiveLine S ↘ S)))
          (ordinaryFiniteConstant A (ProjectiveLine S))
          (Scheme.finiteEtaleTateLine
            (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) κ)
```

The old chart transport is:

```lean
@[irreducible]
def ordinaryFiniteP1DiagonalChartMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    ordinaryFiniteP1DiagonalTarget A N hA S a ⟶
      (ordinaryFinitePushforward A
        (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧) :=
  let e := (projectiveLineDiagonalChart S a).val
  let p := projectiveLineDiagonalProjection S a
  let L := (ordinaryFiniteLine A N hA
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧
  (ordinaryFinitePushforward A p).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e.hom).unit.app L) ≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.hom p).hom.app
      ((ordinaryFinitePullback A e.hom).obj L) ≫
    (rightDerivedLowerStarCongr (ModuleCat.{u + 1} A)
      (projectiveLineDiagonalChart S a).property).hom.app
        ((ordinaryFinitePullback A e.hom).obj L) ≫
    (ordinaryFinitePushforward A
      (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).map
      (ordinaryFiniteShiftedLinePullback A N hA t e.hom
        ((map_natCast
          ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom N) ▸
          hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom)).hom
```

## New

The actual generic constructions and the value-preservation equation are:

```lean
@[implicit_reducible]
def ordinaryFiniteSupportedExt (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  Ext.{u + 1} ((lowerStar (ModuleCat.{u + 1} A) i).obj
    (ordinaryFiniteConstant A D)) F 2

/-- The existing supported realization, on the named ordinary degree-zero objects.
Source: supportedExactDerivedMap for the exact direct image of a closed immersion.
(blueprint: lem-sp-finite-p1-diagonal-kummer-component-formula). -/
@[irreducible]
def ordinaryFiniteSupportedRealization (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (κ : ordinaryFiniteSupportedExt A i F) :
    (ordinaryFinitePushforward A i).obj (ordinaryFiniteUnit A D) ⟶
      (ordinaryFiniteDegreeZero A T F)⟦(2 : ℤ)⟧ :=
  supportedExactDerivedMap (lowerStar (ModuleCat.{u + 1} A) i)
    (ordinaryFiniteConstant A D) F κ


/-- The supported arrow after forgetting support, on the named ordinary objects.
Source: the supported exact realization and canonical constant unit, Stacks 0A45.
(blueprint: lem-sp-finite-p1-diagonal-kummer-component-formula). -/
@[irreducible]
def ordinaryFiniteSupportedArrow (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (κ : ordinaryFiniteSupportedExt A i F) :
    ordinaryFiniteUnit A T ⟶ (ordinaryFiniteDegreeZero A T F)⟦(2 : ℤ)⟧ :=
  supportedDerivedUnit A i ≫ ordinaryFiniteSupportedRealization A i F κ

/-- Factoring the two mapped supported arrows preserves their original composite.
Source: functoriality of direct image and associativity of composition.
(blueprint: lem-sp-finite-p1-diagonal-kummer-component-formula). -/
theorem ordinaryFiniteSupportedArrow_pushforward (A : Type (u + 1)) [CommRing A]
    {D T U : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] (p : T ⟶ U)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (κ : ordinaryFiniteSupportedExt A i F) :
    (supportedDerivedUnit A p ≫
        (ordinaryFinitePushforward A p).map (supportedDerivedUnit A i)) ≫
          (ordinaryFinitePushforward A p).map (ordinaryFiniteSupportedRealization A i F κ) =
      supportedDerivedUnit A p ≫
        (ordinaryFinitePushforward A p).map (ordinaryFiniteSupportedArrow A i F κ) := by
  exact (Category.assoc (supportedDerivedUnit A p)
    ((ordinaryFinitePushforward A p).map (supportedDerivedUnit A i))
    ((ordinaryFinitePushforward A p).map
      (ordinaryFiniteSupportedRealization A i F κ))).trans
    (congrArg (fun f ↦ supportedDerivedUnit A p ≫ f)
      ((ordinaryFinitePushforward A p).map_comp (supportedDerivedUnit A i)
        (ordinaryFiniteSupportedRealization A i F κ)).symm)
```

The supported map retains its original composite:

```lean
@[irreducible]
def ordinaryFiniteP1DiagonalSupportedMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) (a : Bool)
    (κ : ordinaryFiniteSupportedExt A (pullback.diagonal (ProjectiveLine S ↘ S))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA)) :
    ordinaryFiniteUnit A (ProjectiveLine S) ⟶ ordinaryFiniteP1DiagonalTarget A N hA S a :=
  projectiveLineDiagonalAlpha A S a ≫
    (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
      (ordinaryFiniteSupportedRealization A (pullback.diagonal (ProjectiveLine S ↘ S))
        (Scheme.finiteEtaleTateLine
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) κ)
```

The component theorem uses the same named Ext group in its kappa binder.
Unfolding ordinaryFiniteSupportedExt recovers precisely its old Ext type.
Unfolding ordinaryFiniteSupportedRealization recovers supportedExactDerivedMap,
so the supported map has exactly its old value. The component proof factors
this map using ordinaryFiniteSupportedArrow_pushforward; it does not change the
map's definition to the factored form. Supported Chern normalization and class
injectivity identify the supported arrow and the supplied relative Chern arrow.

The chart transport is the same adjunction composite, recorded before specializing the schemes. Its existing signature and irreducibility attribute remain unchanged:

```lean
/-- The canonical adjunction transport around a commuting composition diagram.
Source: adjunction-unit pasting in the projective-line diagonal calculation.
(blueprint: lem-sp-finite-p1-diagonal-kummer-component-formula). -/
@[irreducible]
def ordinaryFiniteChartTransport (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (e : X ⟶ Y) (p : Y ⟶ Z) (r : X ⟶ Z)
    (hr : e ≫ p = r) (L : DerivedCategoryModule A Y) (L' : DerivedCategoryModule A X)
    (v : (ordinaryFinitePullback A e).obj L ⟶ L') :
    (ordinaryFinitePushforward A p).obj L ⟶ (ordinaryFinitePushforward A r).obj L' :=
  (ordinaryFinitePushforward A p).map ((ordinaryFiniteAdjunction A e).unit.app L) ≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e p).hom.app
      ((ordinaryFinitePullback A e).obj L) ≫
    (rightDerivedLowerStarCongr (ModuleCat.{u + 1} A) hr).hom.app
      ((ordinaryFinitePullback A e).obj L) ≫
    (ordinaryFinitePushforward A r).map v

/-- Direct-image transport from either product projection to the standard P1 projection.
This is the comparison preceding the trace in arbitraryBaseFiniteP1DiagonalTrace.
Source: blueprint lem-amb-p1-diagonal-integrals, identification of each projection.
(blueprint: lem-sp-finite-p1-diagonal-kummer-component-formula). -/
@[irreducible]
def ordinaryFiniteP1DiagonalChartMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    ordinaryFiniteP1DiagonalTarget A N hA S a ⟶
      (ordinaryFinitePushforward A
        (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧) :=
  let e := (projectiveLineDiagonalChart S a).val
  let p := projectiveLineDiagonalProjection S a
  let L := (ordinaryFiniteLine A N hA
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧
  ordinaryFiniteChartTransport A e.hom p
    (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)
    (projectiveLineDiagonalChart S a).property L _
      (ordinaryFiniteShiftedLinePullback A N hA t e.hom
        ((map_natCast
          ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom N) ▸
          hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom)).hom
```

## Users

Reviewer (efdbda997e1d): the table below adds the six users of ordinaryFiniteP1DiagonalChartMap that the delivered record omitted.

The item is held by F1. The consumers retain their original signatures. Every existing consumer
retains the same mathematical statement: the named Ext type is definitionally
equal, and the supported map has its original composite after unfolding the realization wrapper.
The original consumers are checked against the same supported composite and chart construction.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals` | unclaimed | Same Ext type; original supported composite through a definitionally equal realization wrapper. |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalChernComponents` | unclaimed | Same Ext type; original supported composite through a definitionally equal realization wrapper. |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula` | F1 | Same Ext type; original supported composite through a definitionally equal realization wrapper. |
| `Sheaf.AlgebraicGeometry.SfP1IntegralTransport` | unclaimed | Same Ext type; original supported composite through a definitionally equal realization wrapper. |
| `Sheaf.AlgebraicGeometry.SfP1ChartExchange` | unclaimed | Uses ordinaryFiniteP1DiagonalChartMap only through the chartMap_compHom statement; compiled against this delivery (reviewer). |
| `Sheaf.AlgebraicGeometry.SfP1ChartMapComposition` | H2 | Its sorry statement chartMap_compHom expands the chart map; the value is unchanged, but a proof must now also unfold ordinaryFiniteChartTransport and ordinaryFiniteAdjunction (both @[irreducible]) to reach derivedUpperStarLowerStarAdjunction and rightDerivedLowerStarComp/Congr. Compiled against this delivery (reviewer). |
| `Sheaf.AlgebraicGeometry.SfP1ProjectionTraceFalseChartPasting` | unclaimed | Uses the chart map only through the chartExchange statement (rw); same type. |
| `Sheaf.AlgebraicGeometry.SfP1ProjectionTraceFalseTail` | unclaimed | Uses the chart map as a term only; same type. |
| `Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransportFalse` | unclaimed | Uses the chart map as a term only; same type. |
| `Sheaf.Paper.TowerP1KernelScalarData` | unclaimed | Uses the chart map as a term only; compiled against this delivery (reviewer). |

## Status

landed 20261026T222636-L-676965 2026-10-26 (merge of deliver/F1/Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula)
