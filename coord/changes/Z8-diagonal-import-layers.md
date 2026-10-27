# AlgebraicGeometry.Etale.projectiveLineDiagonalAlpha

## Reason

The diagonal-unit proof needs the supported component formula below the higher
integral/adjunction import layer. This repair starts from the current F1 proofs,
including the completed Picard theorem, and moves the complete component formula
with its construction interfaces and proof dependencies. Public re-export modules
retain the existing declarations. No mathematical theorem is weakened or replaced
by `sorry`. Definitions used by targets retain their mathematical meaning; their
module ownership and construction representation require the normal independent
statement review.

## Old

```lean
def projectiveLineDiagonalAlpha (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) (a : Bool) :
    ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).obj
        ((ordinaryFinitePushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (ordinaryFiniteUnit A (ProjectiveLine S))) :=
  supportedDerivedUnit A (projectiveLineDiagonalProjection S a) ≫
    (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
      (supportedDerivedUnit A (pullback.diagonal (ProjectiveLine S ↘ S)))
```

```lean
def ordinaryFiniteP1DiagonalTarget (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) (a : Bool) :
    DerivedCategoryModule A (ProjectiveLine S) :=
  (ordinaryFinitePushforward A
    (X := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) (Y := ProjectiveLine S)
    (projectiveLineDiagonalProjection S a)).obj
      ((ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)
```

```lean
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

```lean
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

private theorem base_adjunct_core {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X L : C} {Y M : D} (e : F.obj X ≅ Y) (β : X ⟶ L)
    (v : F.obj L ⟶ M) :
    (adj.unit.app X ≫ G.map e.hom) ≫ G.map (e.inv ≫ F.map β ≫ v) =
      β ≫ adj.unit.app L ≫ G.map v := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← G.map_comp_assoc, Iso.hom_inv_id, G.map_id, Category.id_comp]
  simpa only [Category.assoc] using
    congrArg (fun f => f ≫ G.map v) (adj.unit_naturality β)

private theorem unit_chern_core {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X : C} {Y L : D} (e : F.obj X ⟶ Y) (d : Y ⟶ L) :
    (adj.unit.app X ≫ G.map e) ≫ G.map d = adj.homEquiv X L (e ≫ d) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

private theorem chart_adjunct_core {B C D : Type*} [Category B] [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (R : C ⥤ B) (R' : D ⥤ B) (rc : G ⋙ R ≅ R')
    {X : B} {Y L : C} {Z M : D} (e : F.obj Y ≅ Z)
    (α : X ⟶ R.obj Y) (α' : X ⟶ R'.obj Z)
    (hcomp : α ≫ R.map (adj.unit.app Y ≫ G.map e.hom) ≫ rc.hom.app Z = α')
    (d : Y ⟶ L) (v : F.obj L ⟶ M) :
    α ≫ R.map d ≫ R.map (adj.unit.app L) ≫ rc.hom.app (F.obj L) ≫ R'.map v =
      α' ≫ R'.map (e.inv ≫ F.map d ≫ v) := by
  rw [← hcomp]
  symm
  simp only [Functor.map_comp, Category.assoc]
  rw [← rc.hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← R.map_comp_assoc (G.map e.hom) (G.map e.inv), ← G.map_comp,
    Iso.hom_inv_id, G.map_id, R.map_id, Category.id_comp]
  rw [← rc.hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← R.map_comp_assoc, adj.unit_naturality, R.map_comp]
  simp only [Category.assoc]

private theorem map_sum_components {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    {T : D} {U V : C} (α : T ⟶ F.obj U) (δ b c : U ⟶ V)
    (b' c' : T ⟶ F.obj V) (hsum : δ = b + c)
    (hb : α ≫ F.map b = b') (hc : α ≫ F.map c = c') :
    α ≫ F.map δ = b' + c' := by
  rw [hsum, Functor.map_add, Preadditive.comp_add, hb, hc]

private theorem coefficient_chart_adjunct (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (e : X ⟶ Y) (p : Y ⟶ Z) (r : X ⟶ Z)
    (hr : e ≫ p = r) (L : DerivedCategoryModule A Y) (L' : DerivedCategoryModule A X)
    (d : ordinaryFiniteUnit A Y ⟶ L)
    (v : (ordinaryFinitePullback A e).obj L ⟶ L') :
    supportedDerivedUnit A p ≫ (ordinaryFinitePushforward A p).map d ≫
        ordinaryFiniteChartTransport A e p r hr L L' v =
      supportedDerivedUnit A r ≫ (ordinaryFinitePushforward A r).map
        (ordinaryFiniteArrowPullback A e L L' d v) := by
  unfold ordinaryFiniteChartTransport ordinaryFiniteArrowPullback
  subst r
  rw [rightDerivedLowerStarCongr_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  exact chart_adjunct_core (ordinaryFiniteAdjunction A e)
    (ordinaryFinitePushforward A p) (ordinaryFinitePushforward A (e ≫ p))
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e p)
    (ordinaryFiniteUnitPullback A e) _ _
    (by
      have hc := supportedDerivedUnit_comp A e p
      rw [supportedDerivedUnit_eq A e] at hc
      exact hc) d v

attribute [local semireducible] ordinaryFiniteSupportedRealization
  supportedKummerChern ordinaryFiniteP1KummerClass
  ordinaryFiniteLinePullbackMap ordinaryFiniteP1DiagonalChartMap
  ordinaryFiniteP1Unit ordinaryFiniteP1ChernPushforward ordinaryFiniteP1DiagonalSupportedMap
```

```lean
public import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalData
```


`ProjectiveLineDiagonalData` defines projection, chart and Alpha above Trace.
`FiniteP1DiagonalKummerComponentFormula` publicly imports DiagonalIntegrals and
CoefficientRecords and defines the supported Ext/realization/arrow interfaces,
chart transport, three component maps and the proved component formula.
`FiniteP1DiagonalPicard` publicly imports Data. This path reaches the item through
Trace and Adjunction, so it cannot remain below the relocated component formula.

The current source-unit body is:

```lean
supportedDerivedUnit A (projectiveLineDiagonalProjection S a) ≫
  (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
    (supportedDerivedUnit A (pullback.diagonal (ProjectiveLine S ↘ S)))
```

## New

```lean
def projectiveLineDiagonalAlpha (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) (a : Bool) :
    ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).obj
        ((ordinaryFinitePushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (ordinaryFiniteUnit A (ProjectiveLine S))) :=
  constantSingleSectionUnits (ModuleCat.{u + 1} A)
    (pullback.diagonal (ProjectiveLine S ↘ S)) (projectiveLineDiagonalProjection S a)
    (𝟙_ (ModuleCat.{u + 1} A))
```

```lean
def ordinaryFiniteP1DiagonalTarget (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) (a : Bool) :
    DerivedCategoryModule A (ProjectiveLine S) :=
  (ordinaryFinitePushforward A
    (X := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) (Y := ProjectiveLine S)
    (projectiveLineDiagonalProjection S a)).obj
      ((ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)
```

```lean
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

```lean
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

private theorem base_adjunct_core {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X L : C} {Y M : D} (e : F.obj X ≅ Y) (β : X ⟶ L)
    (v : F.obj L ⟶ M) :
    (adj.unit.app X ≫ G.map e.hom) ≫ G.map (e.inv ≫ F.map β ≫ v) =
      β ≫ adj.unit.app L ≫ G.map v := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← G.map_comp_assoc, Iso.hom_inv_id, G.map_id, Category.id_comp]
  simpa only [Category.assoc] using
    congrArg (fun f => f ≫ G.map v) (adj.unit_naturality β)

private theorem unit_chern_core {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X : C} {Y L : D} (e : F.obj X ⟶ Y) (d : Y ⟶ L) :
    (adj.unit.app X ≫ G.map e) ≫ G.map d = adj.homEquiv X L (e ≫ d) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

private theorem chart_adjunct_core {B C D : Type*} [Category B] [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (R : C ⥤ B) (R' : D ⥤ B) (rc : G ⋙ R ≅ R')
    {X : B} {Y L : C} {Z M : D} (e : F.obj Y ≅ Z)
    (α : X ⟶ R.obj Y) (α' : X ⟶ R'.obj Z)
    (hcomp : α ≫ R.map (adj.unit.app Y ≫ G.map e.hom) ≫ rc.hom.app Z = α')
    (d : Y ⟶ L) (v : F.obj L ⟶ M) :
    α ≫ R.map d ≫ R.map (adj.unit.app L) ≫ rc.hom.app (F.obj L) ≫ R'.map v =
      α' ≫ R'.map (e.inv ≫ F.map d ≫ v) := by
  rw [← hcomp]
  symm
  simp only [Functor.map_comp, Category.assoc]
  rw [← rc.hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← R.map_comp_assoc (G.map e.hom) (G.map e.inv), ← G.map_comp,
    Iso.hom_inv_id, G.map_id, R.map_id, Category.id_comp]
  rw [← rc.hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← R.map_comp_assoc, adj.unit_naturality, R.map_comp]
  simp only [Category.assoc]

private theorem map_sum_components {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    {T : D} {U V : C} (α : T ⟶ F.obj U) (δ b c : U ⟶ V)
    (b' c' : T ⟶ F.obj V) (hsum : δ = b + c)
    (hb : α ≫ F.map b = b') (hc : α ≫ F.map c = c') :
    α ≫ F.map δ = b' + c' := by
  rw [hsum, Functor.map_add, Preadditive.comp_add, hb, hc]

private theorem coefficient_chart_adjunct (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (e : X ⟶ Y) (p : Y ⟶ Z) (r : X ⟶ Z)
    (hr : e ≫ p = r) (L : DerivedCategoryModule A Y) (L' : DerivedCategoryModule A X)
    (d : ordinaryFiniteUnit A Y ⟶ L)
    (v : (ordinaryFinitePullback A e).obj L ⟶ L') :
    supportedDerivedUnit A p ≫ (ordinaryFinitePushforward A p).map d ≫
        ordinaryFiniteChartTransport A e p r hr L L' v =
      supportedDerivedUnit A r ≫ (ordinaryFinitePushforward A r).map
        (ordinaryFiniteArrowPullback A e L L' d v) := by
  unfold ordinaryFiniteChartTransport ordinaryFiniteArrowPullback
  subst r
  rw [rightDerivedLowerStarCongr_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  exact chart_adjunct_core (ordinaryFiniteAdjunction A e)
    (ordinaryFinitePushforward A p) (ordinaryFinitePushforward A (e ≫ p))
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e p)
    (ordinaryFiniteUnitPullback A e) _ _
    (by
      have hc := supportedDerivedUnit_comp A e p
      rw [supportedDerivedUnit_eq A e] at hc
      exact hc) d v

attribute [local semireducible] ordinaryFiniteSupportedRealization
  supportedKummerChern ordinaryFiniteP1KummerClass
  ordinaryFiniteLinePullbackMap ordinaryFiniteP1DiagonalChartMap
  ordinaryFiniteP1Unit ordinaryFiniteP1ChernPushforward ordinaryFiniteP1DiagonalSupportedMap
```

```lean
public import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalMaps
```


Projection and chart move verbatim to `ProjectiveLineDiagonalMaps`. Alpha moves
with F1's declaration-local `DerivedCategoryModule._proof_1/2` and
`ordinaryFiniteClass._proof_1/2/3` instance attributes. Its body is the identical
generic construction:

```lean
constantSingleSectionUnits (ModuleCat.{u + 1} A)
  (pullback.diagonal (ProjectiveLine S ↘ S)) (projectiveLineDiagonalProjection S a)
  (𝟙_ (ModuleCat.{u + 1} A))
```

The complete current formula module moves to `OrdinaryFiniteP1DiagonalComponents`,
replacing its higher integral import by the lower Maps import. The existing public
CoefficientRecords import is retained. The unused KummerMaps dependency is placed
directly in the Integral and ChartExchange statement consumers instead.
This includes `ordinaryFiniteSupportedExt`, `ordinaryFiniteSupportedRealization`,
`ordinaryFiniteSupportedArrow`, `ordinaryFiniteSupportedArrow_pushforward`,
`ordinaryFiniteChartTransport`, the existing three component maps, every private
helper, F1's coefficient local attributes and the complete component theorem proof.
The unused local attribute naming the higher-layer `projectiveLineTraceTransport`
is omitted, since the lower module does not import that constant. A proved
Alpha-to-supported-units equality in `ProjectiveLineDiagonalAlphaUnits` is rewritten before F1's factorization argument. The formula
keeps its `κ : ordinaryFiniteSupportedExt` binder and all other binders. Its node
keeps F1's statement, proof and proof dependencies, changing only the Lean location.
The SupportedMap and ChartMap bodies are exactly current main's bodies.

`FiniteP1DiagonalPicard` changes only its public import from Data to Maps. Its
current complete proof is retained verbatim. The current source has progressed
beyond the hole described in the return. The lower import removes the cycle
Components -> Picard -> Data -> Trace -> Adjunction -> DiagonalUnit -> Triangles ->
Integral -> Components.

Data publicly imports Components and uses the unchanged named target in its trace
and chart-pushforward signatures; it re-exports projection, chart and Alpha.
The historical formula module keeps both original public imports and re-exports
all the moved declarations through its original integral import. Its old local
declarations would otherwise fail with duplicate-declaration errors. All public
signatures, visibility and attributes are retained, modulo the explicitly named
canonical target and current F1 Ext binder already present on main.

## Users

`FiniteP1DiagonalPicard` is F1's current source and its one-import adaptation is
explicitly requested by the landing return. `FiniteP1DiagonalKummerComponentFormula`
is held by F1. The other historical construction modules were unclaimed when moved.
Z8 owns the new lower interfaces and diagonal-unit proof assemblies.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalAlphaUnits` | Z8 | Proves the defining equation from the generic cache to the original supported-unit pair. |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalPicard` | F1 | Only its public import changes from Data to Maps; the current complete proof is retained. |
| `Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals` | unclaimed | Unchanged declaration and canonical map; available through the original public import. |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalAlpha` | unclaimed | One forced proof unfolding changes from `supportedDerivedUnit` to its identical `constantSingleSectionUnits` cache. Signatures and all other lines stay unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalChernComponents` | unclaimed | Unchanged declaration and canonical map; available through the original public import. |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula` | F1 (claimed after relocation) | Forced compatibility adaptation: the unchanged original public integral import now supplies its original declarations from Components. |
| `Sheaf.AlgebraicGeometry.ProEtaleP1DiagonalComponents` | unclaimed | Unchanged declaration and canonical map; available through the original public import. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalChernComponents` | unclaimed | Unchanged declaration and canonical map; available through the original public import. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalData` | unclaimed | Publicly re-exports Maps; remaining definitions unchanged. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals` | unclaimed | Unchanged declaration and canonical map; available through the original public import. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalTraceCalculation` | unclaimed | Unchanged declaration and canonical map; available through the original public import. |
| `Sheaf.Paper.TowerP1EtaleFiniteData` | unclaimed | Unchanged declaration and canonical map; available through the original public import. |
| `Sheaf.Paper.TowerP1EtaleOperations` | unclaimed | Unchanged declaration and canonical map; available through the original public import. |
| `Sheaf.Paper.TowerP1EtaleOriginComparisons` | unclaimed | Unchanged declaration and canonical map; available through the original public import. |
| `Sheaf.Paper.TowerP1EtaleWords` | unclaimed | Unchanged declaration and canonical map; available through the original public import. |
| `Sheaf.Paper.TowerP1FormulaLevelComparisons` | unclaimed | Unchanged declaration and canonical map; available through the original public import. |
| `Sheaf.Paper.TowerP1KernelScalarData` | unclaimed | Unchanged declaration and canonical map; available through the original public import. |
| `Sheaf.Paper.TowerP1ProjectionLevelComparisons` | unclaimed | Unchanged declaration and canonical map; available through the original public import. |
| `Sheaf.Paper.TowerP1ProjectiveCoordinates` | unclaimed | Unchanged declaration and canonical map; available through the original public import. |
| `Sheaf.Paper.TowerP1TriangleFactorization` | unclaimed | Unchanged declaration and canonical map; available through the original public import. |
| `Sheaf.Paper.TowerP1TriangleWords` | unclaimed | Unchanged declaration and canonical map; available through the original public import. |


The consumer table is retained from the original downstream declaration scan.
The new Picard consumer uses only the relocated chart. Chart exchange now unfolds
`ordinaryFiniteChartTransport` and `ordinaryFiniteAdjunction` to identify the
canonical map with the generic chart transport. The triangle assembly uses
`ordinaryFiniteSupportedRealization` in its local supported arrow and cancellation.
Both adaptations leave their public theorem signatures unchanged.

## Alpha consumer adaptation

`FiniteP1DiagonalAlpha` is unclaimed. Its original proof's
`unfold supportedDerivedUnit` fails after unfolding cached Alpha, because that
identifier no longer occurs. Replacing it with `constantSingleSectionUnits`
exposes the same two single-object units. Its public signatures, visibility,
attributes and imports are retained.

## Status

landed 20261027T135451-L-3711227 2026-10-27 (merge of deliver/Z8/Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalUnit)

The formula node's former statement dependency on the higher diagonal-integral
node is replaced by the lower component-construction node, which now provides
its target and maps. Keeping the higher edge caused a DAG cycle through Trace,
Adjunction and this item even though the Lean import graph was acyclic. This is
a statement-interface dependency correction only: the formula's mathematical
statement, numbered proof steps and proof dependencies are preserved verbatim.
