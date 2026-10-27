# ChartFiniteRing canonical normalization definitions

## Reason

Make the canonical comparison naturality explicit and control elaboration of concrete
module tensor instances. The coefficient category stays explicit in the new generic
comparison definitions. The three old components retain the same source and target and
use the same tower, pullback, shift, tensor and degree-zero maps. No sign or freely
chosen isomorphism is introduced. The only external consumer uses the component without
unfolding it. Targets using this normalization require the usual independent statement
review of its defining maps.

## Old

```lean
@[irreducible]
def affineRightNormalComponent (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (flat : ∀ (T : Scheme.{u}) (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ),
      ObjectProperty.flat (Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)))
    (Y : Scheme.{u}) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ)
    (K : Etale.DerivedCategoryModule R Y) :=
  let t := Scheme.finiteEtaleTwistPullbackData R N hN hR
  let E := fun (T : Scheme.{u}) (d : ℕ) ↦ Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)
  let c := fun {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) ↦
    t.c f hY (affineTracePullbackInvertible N f hY) d
  let prod (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
      ((curriedTensor (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))).obj (E T d)).obj
        (E T 1) ≅ E T (d + 1) :=
    t.p T hT d 1 ≪≫ eqToIso
      (congrArg (Scheme.finiteEtaleTateSheaf R N T hR) (by omega))
  (Etale.ChartFiniteRingNormalization.towerENormalForm (ModuleCat.{u + 1} R)
    N E c (fun T ↦ Iso.refl (E T 0)) flat prod Y hY d).app K

/-- The canonical ordinary chart normalization, pulling the Tate power through e*.
Source: Charts paragraph, geometric identification
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def etaleChartNormalComponent (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (flat : ∀ (T : Scheme.{u}) (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ),
      ObjectProperty.flat (Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)))
    {U Y : Scheme.{u}} (hY : IsUnit (N : Γ(Y, ⊤)))
    (d : ℕ) (e : U ⟶ affineTraceTower Y d)
    (K : Etale.DerivedCategoryModule R Y) :=
  (Etale.ordinaryFinitePullback R e).mapIso
      (affineRightNormalComponent R N hN hR flat Y hY d K) ≪≫
    (Etale.ChartFiniteRingNormalization.tensorEPullback (ModuleCat.{u + 1} R) N
      (fun T d ↦ Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ))
      (fun f hT d ↦ (Scheme.finiteEtaleTwistPullbackData R N hN hR).c f hT
        (affineTracePullbackInvertible N f hT) d)
      e (affineTraceInvertible N Y hY d) d (2 * (d : ℤ))).app
        ((Etale.ordinaryFinitePullback R (affineTraceProjection Y d)).obj K) ≪≫
    (Etale.derivedTensorRight (ModuleCat.{u + 1} R) U
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf R N U hR (d : ℤ))) ⋙
      shiftFunctor _ (2 * (d : ℤ))).mapIso
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} R) e
          (affineTraceProjection Y d)).symm.app K)

/-- The fixed comparison component from the ordinary ordered chart functor to the
geometric pro-etale functor: normal form, shift, monoidality, degree-zero Tate
comparison, and the canonical site/pullback interchange. No isomorphism is chosen.
Source: Charts paragraph, geometric identification
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def chartGeometryComponent (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (flat : ∀ (T : Scheme.{u}) (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ),
      ObjectProperty.flat (Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)))
    {U Y : Scheme.{u}} (hY : IsUnit (N : Γ(Y, ⊤)))
    (d : ℕ) (e : U ⟶ affineTraceTower Y d) (K : Etale.DerivedCategoryModule R Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory.obj
        ((Etale.affineTraceRight R N hR Y d ⋙ Etale.ordinaryFinitePullback R e).obj K) ≅
      (geometricRight R N hR d e).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategory.obj K) := by
  let C := (comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory
  let f := e ≫ affineTraceProjection Y d
  let L := (_root_.DerivedCategory.singleFunctor _ 0).obj
    (Scheme.finiteEtaleTateSheaf R N U hR (d : ℤ))
  let P := (Etale.ordinaryFinitePullback R f).obj K
  let square :
      (comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategory ⋙
          (upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory ≅
        (Etale.upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory ⋙ C :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} R) f) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  let pb := C.mapIso ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} R) f).app K) ≪≫
      square.symm.app K
  exact C.mapIso (etaleChartNormalComponent R N hN hR flat hY d e K) ≪≫
    (C.commShiftIso (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
          (ModuleCat.{u + 1} R) P).app L ≪≫
        ((derivedTensor (ModuleCat.{u + 1} R) U).mapIso pb).app _ ≪≫
        ((derivedTensor (ModuleCat.{u + 1} R) U).obj _).mapIso
          (((comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategorySingleFunctor
            0).app (Scheme.finiteEtaleTateSheaf R N U hR (d : ℤ))))
```

## New

```lean
/-- The canonical coordinate-tower normalization, retaining the actual tensor, shift,
pullback and Tate-product maps that the existence theorem forgets.
Source: Charts paragraph, geometric identification; affine normal-form induction
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def affineRightNormalIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (flat : ∀ (T : Scheme.{u}) (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ),
      ObjectProperty.flat (Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)))
    (Y : Scheme.{u}) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :=
  let t := Scheme.finiteEtaleTwistPullbackData R N hN hR
  let E := fun (T : Scheme.{u}) (d : ℕ) ↦ Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)
  let c := fun {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) ↦
    t.c f hY (affineTracePullbackInvertible N f hY) d
  let prod (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
      ((curriedTensor (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))).obj (E T d)).obj
        (E T 1) ≅ E T (d + 1) :=
    t.p T hT d 1 ≪≫ eqToIso
      (congrArg (Scheme.finiteEtaleTateSheaf R N T hR) (by omega))
  (Etale.ChartFiniteRingNormalization.towerENormalForm (ModuleCat.{u + 1} R)
    N E c (fun T ↦ Iso.refl (E T 0)) flat prod Y hY d)


/-- The canonical coordinate-tower normalization, retaining the actual tensor, shift,
pullback and Tate-product maps that the existence theorem forgets.
Source: Charts paragraph, geometric identification; affine normal-form induction
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def affineRightNormalComponent (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (flat : ∀ (T : Scheme.{u}) (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ),
      ObjectProperty.flat (Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)))
    (Y : Scheme.{u}) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ)
    (K : Etale.DerivedCategoryModule R Y) :=
  (affineRightNormalIso R N hN hR flat Y hY d).app K

/-- The canonical ordinary chart normalization, pulling the Tate power through e*.
Source: Charts paragraph, geometric identification
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def etaleChartNormalIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (flat : ∀ (T : Scheme.{u}) (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ),
      ObjectProperty.flat (Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)))
    {U Y : Scheme.{u}} (hY : IsUnit (N : Γ(Y, ⊤)))
    (d : ℕ) (e : U ⟶ affineTraceTower Y d) :
    Etale.affineTraceRight R N hR Y d ⋙ Etale.ordinaryFinitePullback R e ≅
      Etale.ordinaryFinitePullback R (e ≫ affineTraceProjection Y d) ⋙
        Etale.derivedTensorRight (ModuleCat.{u + 1} R) U
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateSheaf R N U hR (d : ℤ))) ⋙
        shiftFunctor _ (2 * (d : ℤ)) :=
  let t := Scheme.finiteEtaleTwistPullbackData R N hN hR
  let E := fun (T : Scheme.{u}) (d : ℕ) ↦ Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)
  let c := fun {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) ↦
    t.c f hY (affineTracePullbackInvertible N f hY) d
  let prod (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
      ((curriedTensor (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))).obj (E T d)).obj
        (E T 1) ≅ E T (d + 1) :=
    t.p T hT d 1 ≪≫ eqToIso
      (congrArg (Scheme.finiteEtaleTateSheaf R N T hR) (by omega))
  Etale.ChartFiniteRingNormalization.chartENormalForm (ModuleCat.{u + 1} R)
    N E c (fun T ↦ Iso.refl (E T 0)) flat prod hY d e

/-- The canonical ordinary chart normalization, pulling the Tate power through e*.
Source: Charts paragraph, geometric identification
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def etaleChartNormalComponent (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (flat : ∀ (T : Scheme.{u}) (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ),
      ObjectProperty.flat (Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)))
    {U Y : Scheme.{u}} (hY : IsUnit (N : Γ(Y, ⊤)))
    (d : ℕ) (e : U ⟶ affineTraceTower Y d)
    (K : Etale.DerivedCategoryModule R Y) :=
  (etaleChartNormalIso R N hN hR flat hY d e).app K

/-- Flip a tensor comparison with its coefficient categories fixed.
Source: functor naturality (blueprint: lem-sp-chart-finite-ring-adjunction). -/
def flipTensorComparison {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D) (F : C ⥤ D)
    (h : (Functor.postcompose₂.obj F).obj T ≅
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj S) (L : C) :
    T.flip.obj L ⋙ F ≅ F ⋙ S.flip.obj (F.obj L) :=
  NatIso.ofComponents (fun K ↦ (h.app K).app L)
    (fun f ↦ congr_app (h.hom.naturality f) L)

/-- The canonical monoidal comparison with a fixed right tensor factor.
Source: Charts paragraph, the monoidal site comparison
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def chartTensorComparison
    (B : Type v) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (U : Scheme.{u}) [(comparisonUpperStar B U).PreservesFlat]
    (L : _root_.DerivedCategory (Sheaf U.smallEtaleTopology B)) :
    Etale.derivedTensorRight B U L ⋙ (comparisonUpperStar B U).mapDerivedCategory ≅
      (comparisonUpperStar B U).mapDerivedCategory ⋙
        (derivedTensor B U).flip.obj ((comparisonUpperStar B U).mapDerivedCategory.obj L) :=
  let C := comparisonUpperStar B U
  let j := flipTensorComparison (Etale.derivedTensor B U) (derivedTensor B U)
    C.leftDerivedFunctor (asIso C.leftDerivedTensorComparison) L
  Functor.isoWhiskerLeft _ C.leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    j ≪≫ Functor.isoWhiskerRight C.leftDerivedFunctorIsoMapDerivedCategory _ ≪≫
    Functor.isoWhiskerLeft C.mapDerivedCategory
      ((derivedTensor B U).flip.mapIso (C.leftDerivedFunctorIsoMapDerivedCategory.app L))


/-- Canonical site, tensor and shift comparison with a generic coefficient category.
The coefficient category stays explicit to avoid expanding the module tensor construction.
Source: Charts paragraph, geometric identification
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def chartGeometryComparison
    (B : Type v) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {U Y : Scheme.{u}} (f : U ⟶ Y) [(Etale.upperStar B f).PreservesFlat]
    [(comparisonUpperStar B U).PreservesFlat]
    (L : Sheaf U.smallEtaleTopology B) (b : ℤ) :
    ((Etale.upperStar B f).leftDerivedFunctor ⋙
        Etale.derivedTensorRight B U ((_root_.DerivedCategory.singleFunctor _ 0).obj L) ⋙
        shiftFunctor _ b) ⋙ (comparisonUpperStar B U).mapDerivedCategory ≅
      (comparisonUpperStar B Y).mapDerivedCategory ⋙
        (upperStar B f).mapDerivedCategory ⋙
          (derivedTensor B U).flip.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((comparisonUpperStar B U).obj L)) ⋙ shiftFunctor _ b :=
  let C := (comparisonUpperStar B U).mapDerivedCategory
  let square :
      (comparisonUpperStar B Y).mapDerivedCategory ⋙ (upperStar B f).mapDerivedCategory ≅
        (Etale.upperStar B f).mapDerivedCategory ⋙ C :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (comparisonUpperStarCompUpperStarIso B f) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  let pb := Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory B f) C ≪≫ square.symm
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (C.commShiftIso b) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (chartTensorComparison B U ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) _ ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight pb _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight ((derivedTensor B U).flip.mapIso
        (((comparisonUpperStar B U).mapDerivedCategorySingleFunctor 0).app L)) _))


/-- Compose a chart normal form with the canonical comparison of sites.
Source: Charts paragraph, geometric identification
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def chartGeometryWithNormalForm
    (B : Type v) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {U Y : Scheme.{u}} (f : U ⟶ Y) [(Etale.upperStar B f).PreservesFlat]
    [(comparisonUpperStar B U).PreservesFlat]
    (L : Sheaf U.smallEtaleTopology B) (b : ℤ)
    (H : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology B) ⥤
      _root_.DerivedCategory (Sheaf U.smallEtaleTopology B))
    (j : H ≅ (Etale.upperStar B f).leftDerivedFunctor ⋙
      Etale.derivedTensorRight B U ((_root_.DerivedCategory.singleFunctor _ 0).obj L) ⋙
        shiftFunctor _ b) :=
  Functor.isoWhiskerRight j (comparisonUpperStar B U).mapDerivedCategory ≪≫
    chartGeometryComparison B f L b

/-- The canonical chart comparison as a natural isomorphism.
Source: Charts paragraph, coordinate normalization and site comparison
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def chartGeometryIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (flat : ∀ (T : Scheme.{u}) (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ),
      ObjectProperty.flat (Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)))
    {U Y : Scheme.{u}} (hY : IsUnit (N : Γ(Y, ⊤)))
    (d : ℕ) (e : U ⟶ affineTraceTower Y d) :
    (Etale.affineTraceRight R N hR Y d ⋙ Etale.ordinaryFinitePullback R e) ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategory ⋙
        geometricRight R N hR d e :=
  chartGeometryWithNormalForm (ModuleCat.{u + 1} R) (e ≫ affineTraceProjection Y d)
    (Scheme.finiteEtaleTateSheaf R N U hR (d : ℤ)) (2 * (d : ℤ)) _
    (etaleChartNormalIso R N hN hR flat hY d e)

/-- The fixed comparison component from the ordinary ordered chart functor to the
geometric pro-etale functor: normal form, shift, monoidality, degree-zero Tate
comparison, and the canonical site/pullback interchange. No isomorphism is chosen.
Source: Charts paragraph, geometric identification
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def chartGeometryComponent (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (flat : ∀ (T : Scheme.{u}) (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ),
      ObjectProperty.flat (Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)))
    {U Y : Scheme.{u}} (hY : IsUnit (N : Γ(Y, ⊤)))
    (d : ℕ) (e : U ⟶ affineTraceTower Y d) (K : Etale.DerivedCategoryModule R Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory.obj
        ((Etale.affineTraceRight R N hR Y d ⋙ Etale.ordinaryFinitePullback R e).obj K) ≅
      (geometricRight R N hR d e).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategory.obj K) :=
  (chartGeometryIso R N hN hR flat hY d e).app K
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | G4 | Naturality uses components of natural isomorphisms. |
| Sheaf.Paper.ChartCounitScalarTransport | unclaimed | Same component endpoints; overlay compile passed. |
| Sheaf.AlgebraicGeometry.AffineTraceRightNormalForm | unclaimed | Exposes the proved shared construction. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Exposes its categorical proof; original theorem unchanged. |
| Sheaf.Paper.OrderedAffineTraceNormalForm | unclaimed | Same helpers; overlay compile passed. |

## Status

landed 20261025T013919-L-4036767 2026-10-25 (merge of deliver/G4/Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction)

## Shared normalization implementation

`Sheaf.AlgebraicGeometry.AffineTraceRightNormalForm` is unclaimed (no current
claim record matching that module). Its eleven generic coordinate-normalization
helpers are made public, with their signatures, attributes, and bodies unchanged. Each exposed helper receives a source
docstring attached to the existing normal-form node.
Two existing imports are made public because exposed definitions use them. The
item's existing helper names now delegate to these constructions with the same
arguments, avoiding duplicate kernel checking of the induction. The helpers are
attached to their existing normal-form node; no new mathematical assertion is added.

The downstream search finds 1673 import descendants. Searching each of the eleven
helper names finds no external textual user beyond the item and
`Sheaf.Paper.OrderedAffineTraceNormalForm`. The only textual users of
`towerENormalForm` are this module itself, the item, and
`Sheaf.Paper.OrderedAffineTraceNormalForm`; the latter already imports all of this
module and calls precisely the same helper. Visibility addition preserves those
uses. No existing signature or statement changes. The unchanged `OrderedAffineTraceNormalForm` consumer compiled in the same
remote compile set as the modified helper owner (exit 0). Its original
`import all` access to the remaining private helpers stays intact. The item and its unchanged `ChartCounitScalarTransport` consumer also compile
together with both modified owners in the final sandbox batch (exit 0 throughout).

## Shared adjunction transfer construction

`Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` is unclaimed. The new proved
`etaleProEtaleAdjunctionTransferOfComparison` exposes the categorical argument
already used in that file, without the geometric hypotheses or unused normalization
equality. The original theorem retains its full signature and now applies this
construction. The item applies it to its actual fixed compact-support comparison.
No axioms, unproved declarations or new mathematical assumptions are introduced.
The owner compiles with its original theorem applying the exposed helper (exit 0
in the paired and full-sandbox remote batches).
The source is the same existing transfer node; its Lean attachment includes the helper.
Consumers of the original theorem retain its signature and meaning.

## Duplicate aliases

The item namespace retains its eleven helper names as direct abbreviations of
the exposed original helpers. Their coefficient category type is inherited from
the original rather than restated through separately synthesized instances.
This preserves the canonical construction and avoids repeated instance conversion
in every helper. The only external item consumer refers to `chartGeometryComponent`,
whose explicit source and target remain intact. No target declaration changes.

The transfer owner also proves `transportUniqueCounitIso`, a general categorical
transport of a unique counit-preserving comparison along a specified source
isomorphism. Its proof is the elementary isomorphism calculation formerly copied
into the item. It introduces no hypothesis into the original transfer theorem.

## Duplicate alias definitions (verbatim)

Old:

```lean
namespace AlgebraicGeometry.Etale.ChartFiniteRingNormalization
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

/-- Canonical shiftedComp comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def shiftedComp {C : Type v} [Category.{w} C] [HasShift C ℤ]
    (F G H : C ⥤ C) [G.CommShift ℤ] (e : F ⋙ G ≅ H) (a b : ℤ) :
    (F ⋙ shiftFunctor _ a) ⋙ (G ⋙ shiftFunctor _ b) ≅
      H ⋙ shiftFunctor _ (a + b) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.commShiftIso a) _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e _ ≪≫
    Functor.isoWhiskerLeft _ (shiftFunctorAdd _ a b).symm

/-- Canonical tensorShiftCompGeneral comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def tensorShiftCompGeneral
    (B : Type v) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (X : Scheme.{u})
    (L M : DerivedCategory (Sheaf X.smallEtaleTopology B)) (a b : ℤ) :
    (derivedTensorRight B X L ⋙ shiftFunctor _ a) ⋙
        (derivedTensorRight B X M ⋙ shiftFunctor _ b) ≅
      derivedTensorRight B X (((derivedTensor B X).obj L).obj M) ⋙ shiftFunctor _ (a + b) :=
  shiftedComp _ _ _ (tensorRightTensor L M).symm a b

/-- Canonical comparison of the derived product of two degree-zero sheaves, with
flat first factor, to their ordinary tensor product followed by the fixed Tate product.
Source: Charts paragraph, the affine Tate normal form
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def singleProductGeneral
    (B : Type v) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (X : Scheme.{u})
    (L M V : Sheaf X.smallEtaleTopology B) (hL : ObjectProperty.flat L)
    (e : ((curriedTensor (Sheaf X.smallEtaleTopology B)).obj L).obj M ≅ V) :
    ((derivedTensor B X).obj ((DerivedCategory.singleFunctor _ 0).obj L)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj V :=
  singleFunctorObjTensorIso L M hL ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e

/-- Canonical lineShiftGeneral comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def lineShiftGeneral
    (B : Type v) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {U P S : Scheme.{u}} (j : U ⟶ P) (q : P ⟶ S) (p : U ⟶ S)
    (w : j ≫ q = p) [(upperStar B j).PreservesFlat]
    (L : DerivedCategory (Sheaf P.smallEtaleTopology B))
    (M : DerivedCategory (Sheaf U.smallEtaleTopology B))
    (e : (upperStar B j).leftDerivedFunctor.obj L ≅ M⟦(2 : ℤ)⟧) :
    ((upperStar B q).leftDerivedFunctor ⋙ derivedTensorRight B P L) ⋙
        (upperStar B j).leftDerivedFunctor ≅
      (upperStar B p).leftDerivedFunctor ⋙ derivedTensorRight B U M ⋙
        shiftFunctor _ (2 : ℤ) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (derivedTensorRightCompLeftDerivedUpperStarIso B j L ≪≫
        Functor.isoWhiskerLeft _
          ((derivedTensorRightFunctor B U).mapIso e ≪≫ derivedTensorRightShiftIso B M 2)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarComp B j q p w.symm).symm _

section General
variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  (N : ℕ) (E : ∀ X : Scheme.{u}, ℕ → Sheaf X.smallEtaleTopology B)
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (upperStar B f).PreservesFlat]

/-- Canonical singleE comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev singleE (X : Scheme.{u}) (d : ℕ) :=
  (DerivedCategory.singleFunctor _ 0).obj (E X d)

/-- Canonical lineR comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev lineR (X : Scheme.{u}) :=
  ((upperStar B (ProjectiveLine X ↘ X)).leftDerivedFunctor ⋙
    derivedTensorRight B (ProjectiveLine X) ((singleE B E (ProjectiveLine X) 1)⟦(2 : ℤ)⟧)) ⋙
      (upperStar B (ProjectiveLine.affineChart X)).leftDerivedFunctor

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsUnit (N : Γ(Y, ⊤)) → ∀ d : ℕ,
  (upperStar B f).obj (E Y d) ≅ E X d)

/-- Canonical singleEPullback comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def singleEPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :
    (upperStar B f).leftDerivedFunctor.obj (singleE B E Y d) ≅ singleE B E X d :=
  (singleFunctorCompLeftDerivedUpperStarIso B f).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (c f hY d)

/-- Canonical tensorEPullback comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def tensorEPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) (a : ℤ) :
    (derivedTensorRight B Y (singleE B E Y d) ⋙ shiftFunctor _ a) ⋙
        (upperStar B f).leftDerivedFunctor ≅
      (upperStar B f).leftDerivedFunctor ⋙ derivedTensorRight B X (singleE B E X d) ⋙
        shiftFunctor _ a :=
  letI := commShiftLeftDerivedUpperStar B f
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((upperStar B f).leftDerivedFunctor.commShiftIso a) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedTensorRightCompLeftDerivedUpperStarIso B f _) _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      ((derivedTensorRightFunctor B X).mapIso (singleEPullback B N E c f hY d)) _)

/-- Canonical lineENormalForm comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def lineENormalForm (X : Scheme.{u}) (hX : IsUnit (N : Γ(X, ⊤))) :
    lineR B E X ≅ (upperStar B (AffineSpace PUnit.{u + 1} X ↘ X)).leftDerivedFunctor ⋙
      derivedTensorRight B (AffineSpace PUnit.{u + 1} X)
        (singleE B E (AffineSpace PUnit.{u + 1} X) 1) ⋙ shiftFunctor _ (2 : ℤ) := by
  let j := ProjectiveLine.affineChart X
  letI := commShiftLeftDerivedUpperStar B j
  apply lineShiftGeneral B j (ProjectiveLine X ↘ X)
    (AffineSpace PUnit.{u + 1} X ↘ X) (ProjectiveLine.affineChart_over X)
  exact ((upperStar B j).leftDerivedFunctor.commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      (singleEPullback B N E c j (affineTraceProjectiveInvertible N X hX) 1)

variable (e0 : ∀ X : Scheme.{u}, E X 0 ≅ (constantSheaf X.smallEtaleTopology B).obj (𝟙_ B))
  (flat : ∀ X : Scheme.{u}, IsUnit (N : Γ(X, ⊤)) → ∀ d, ObjectProperty.flat (E X d))
  (prod : ∀ X : Scheme.{u}, IsUnit (N : Γ(X, ⊤)) → ∀ d : ℕ,
    ((curriedTensor (Sheaf X.smallEtaleTopology B)).obj (E X d)).obj (E X 1) ≅ E X (d + 1))

/-- Degree-zero Tate multiplication in the derived category, with its flatness
witness and the normalized ordinary Tate product kept as separate inputs.
Source: Charts paragraph, the affine Tate normal form
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def productE (X : Scheme.{u}) (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) :
    ((derivedTensor B X).obj (singleE B E X d)).obj (singleE B E X 1) ≅
      singleE B E X (d + 1) :=
  singleProductGeneral B X _ _ _ (flat X hX d) (prod X hX d)

/-- Canonical towerENormalForm comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def towerENormalForm (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    affineTraceRightTower (fun e ↦ lineR B E (affineTraceTower S e)) d ≅
      (upperStar B (affineTraceProjection S d)).leftDerivedFunctor ⋙
        derivedTensorRight B (affineTraceTower S d) (singleE B E (affineTraceTower S d) d) ⋙
          shiftFunctor _ (2 * (d : ℤ)) := by
  induction d with
  | zero =>
    let e : derivedTensorRight B S (singleE B E S 0) ≅ 𝟭 _ :=
      (derivedTensorRightFunctor B S).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso (e0 S) ≪≫ singleFunctorObjUnitIso B S) ≪≫
          derivedTensorRightUnitorNatIso B S
    exact (Functor.isoWhiskerRight (leftDerivedUpperStarId B S) _ ≪≫
      Functor.leftUnitor _ ≪≫ Functor.isoWhiskerRight e _ ≪≫
        Functor.leftUnitor _ ≪≫ shiftFunctorZero _ ℤ).symm
  | succ d ih =>
    let T := affineTraceTower S d
    let U := affineTraceTower S (d + 1)
    let p := AffineSpace PUnit.{u + 1} T ↘ T
    let P := (upperStar B (affineTraceProjection S d)).leftDerivedFunctor
    let Q := (upperStar B p).leftDerivedFunctor
    let L := singleE B E U d
    let M := singleE B E U 1
    let k : (derivedTensorRight B U L ⋙ shiftFunctor _ (2 * (d : ℤ))) ⋙
        (derivedTensorRight B U M ⋙ shiftFunctor _ (2 : ℤ)) ≅
        derivedTensorRight B U (singleE B E U (d + 1)) ⋙
          shiftFunctor _ (2 * ((d + 1 : ℕ) : ℤ)) :=
      tensorShiftCompGeneral B U L M (2 * (d : ℤ)) 2 ≪≫
      Functor.isoWhiskerRight ((derivedTensorRightFunctor B U).mapIso
        (productE B N E flat prod U (affineTraceInvertible N S hS (d + 1)) d)) _ ≪≫
      Functor.isoWhiskerLeft _ (eqToIso (by congr 1))
    exact Functor.isoWhiskerRight ih (lineR B E T) ≪≫
      Functor.isoWhiskerLeft _
        (lineENormalForm B N E c T (affineTraceInvertible N S hS d)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft P
        ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (tensorEPullback B N E c p (affineTraceInvertible N S hS d) d (2 * (d : ℤ))) _ ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Q k) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (leftDerivedUpperStarComp B p (affineTraceProjection S d)).symm _

end General
```

New:

```lean
namespace AlgebraicGeometry.Etale.ChartFiniteRingNormalization
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

/-- Canonical shiftedComp comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev shiftedComp := @_root_.AlgebraicGeometry.Etale.shiftedComp

/-- Canonical tensorShiftCompGeneral comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev tensorShiftCompGeneral := @_root_.AlgebraicGeometry.Etale.tensorShiftCompGeneral

/-- Canonical comparison of the derived product of two degree-zero sheaves, with
flat first factor, to their ordinary tensor product followed by the fixed Tate product.
Source: Charts paragraph, the affine Tate normal form
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev singleProductGeneral := @_root_.AlgebraicGeometry.Etale.singleProductGeneral

/-- Canonical lineShiftGeneral comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev lineShiftGeneral := @_root_.AlgebraicGeometry.Etale.lineShiftGeneral

/-- Canonical singleE comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev singleE := @_root_.AlgebraicGeometry.Etale.singleE

/-- Canonical lineR comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev lineR := @_root_.AlgebraicGeometry.Etale.lineR

/-- Canonical singleEPullback comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev singleEPullback := @_root_.AlgebraicGeometry.Etale.singleEPullback

/-- Canonical tensorEPullback comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev tensorEPullback := @_root_.AlgebraicGeometry.Etale.tensorEPullback

/-- Canonical lineENormalForm comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev lineENormalForm := @_root_.AlgebraicGeometry.Etale.lineENormalForm

/-- Degree-zero Tate multiplication in the derived category, with its flatness
witness and the normalized ordinary Tate product kept as separate inputs.
Source: Charts paragraph, the affine Tate normal form
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev productE := @_root_.AlgebraicGeometry.Etale.productE

/-- Canonical towerENormalForm comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev towerENormalForm := @_root_.AlgebraicGeometry.Etale.towerENormalForm

```

## Exact changes in the shared owners

The following diffs give the old and new owner declarations verbatim.

### lean/Sheaf/AlgebraicGeometry/AffineTraceRightNormalForm.lean

```diff
--- Old
+++ New
@@ -6,11 +6,11 @@
 module
 
 public import Sheaf.AlgebraicGeometry.AffineTraceConstruction
-import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
+public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
 import WeilConjectures.SixFunctors.Etale.Derived.Invertible
 import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
 import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
-import WeilConjectures.SixFunctors.Etale.Derived.TensorRightUnitor
+public import WeilConjectures.SixFunctors.Etale.Derived.TensorRightUnitor
 
 /-!
 # AffineTraceRightNormalForm
@@ -27,8 +27,11 @@
 
 attribute [local instance] Sheaf.monoidalCategory
 
-@[irreducible]
-private def shiftedComp {C : Type*} [Category C] [HasShift C ℤ]
+/-- The specified shiftedComp construction used by the affine trace normal form.
+Source: blueprint sk-prop-an, Steps 5(b) and 6
+(blueprint: lem-amb-affine-trace-right-normal-form). -/
+@[irreducible]
+def shiftedComp {C : Type*} [Category C] [HasShift C ℤ]
     (F G H : C ⥤ C) [G.CommShift ℤ] (e : F ⋙ G ≅ H) (a b : ℤ) :
     (F ⋙ shiftFunctor _ a) ⋙ (G ⋙ shiftFunctor _ b) ≅
       H ⋙ shiftFunctor _ (a + b) :=
@@ -40,8 +43,11 @@
     Functor.isoWhiskerRight e _ ≪≫
     Functor.isoWhiskerLeft _ (shiftFunctorAdd _ a b).symm
 
-@[irreducible]
-private def tensorShiftCompGeneral
+/-- The specified tensorShiftCompGeneral construction used by the affine trace normal form.
+Source: blueprint sk-prop-an, Steps 5(b) and 6
+(blueprint: lem-amb-affine-trace-right-normal-form). -/
+@[irreducible]
+def tensorShiftCompGeneral
     (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
     [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
     [Abelian.HasFunctorialFlatResolution B] (X : Scheme.{u})
@@ -51,8 +57,11 @@
       derivedTensorRight B X (((derivedTensor B X).obj L).obj M) ⋙ shiftFunctor _ (a + b) :=
   shiftedComp _ _ _ (tensorRightTensor L M).symm a b
 
-@[irreducible]
-private def singleProductGeneral
+/-- The specified singleProductGeneral construction used by the affine trace normal form.
+Source: blueprint sk-prop-an, Steps 5(b) and 6
+(blueprint: lem-amb-affine-trace-right-normal-form). -/
+@[irreducible]
+def singleProductGeneral
     (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
     [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
     [Abelian.HasFunctorialFlatResolution B] (X : Scheme.{u})
@@ -74,8 +83,11 @@
   ((derivedTensor B X).mapIso (singleFunctorObjUnitIso B X)).app L ≪≫
     derivedTensorLeftUnitor B X L
 
-@[irreducible]
-private def lineShiftGeneral
+/-- The specified lineShiftGeneral construction used by the affine trace normal form.
+Source: blueprint sk-prop-an, Steps 5(b) and 6
+(blueprint: lem-amb-affine-trace-right-normal-form). -/
+@[irreducible]
+def lineShiftGeneral
     (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
     [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
     [Abelian.HasFunctorialFlatResolution B]
@@ -103,10 +115,16 @@
   (N : ℕ) (E : ∀ X : Scheme.{u}, ℕ → Sheaf X.smallEtaleTopology B)
   [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (upperStar B f).PreservesFlat]
 
-private abbrev singleE (X : Scheme.{u}) (d : ℕ) :=
+/-- The specified singleE construction used by the affine trace normal form.
+Source: blueprint sk-prop-an, Steps 5(b) and 6
+(blueprint: lem-amb-affine-trace-right-normal-form). -/
+abbrev singleE (X : Scheme.{u}) (d : ℕ) :=
   (DerivedCategory.singleFunctor _ 0).obj (E X d)
 
-private abbrev lineR (X : Scheme.{u}) :=
+/-- The specified lineR construction used by the affine trace normal form.
+Source: blueprint sk-prop-an, Steps 5(b) and 6
+(blueprint: lem-amb-affine-trace-right-normal-form). -/
+abbrev lineR (X : Scheme.{u}) :=
   ((upperStar B (ProjectiveLine X ↘ X)).leftDerivedFunctor ⋙
     derivedTensorRight B (ProjectiveLine X) ((singleE B E (ProjectiveLine X) 1)⟦(2 : ℤ)⟧)) ⋙
       (upperStar B (ProjectiveLine.affineChart X)).leftDerivedFunctor
@@ -114,15 +132,21 @@
 variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsUnit (N : Γ(Y, ⊤)) → ∀ d : ℕ,
   (upperStar B f).obj (E Y d) ≅ E X d)
 
-@[irreducible]
-private def singleEPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
+/-- The specified singleEPullback construction used by the affine trace normal form.
+Source: blueprint sk-prop-an, Steps 5(b) and 6
+(blueprint: lem-amb-affine-trace-right-normal-form). -/
+@[irreducible]
+def singleEPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
     (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :
     (upperStar B f).leftDerivedFunctor.obj (singleE B E Y d) ≅ singleE B E X d :=
   (singleFunctorCompLeftDerivedUpperStarIso B f).app _ ≪≫
     (DerivedCategory.singleFunctor _ 0).mapIso (c f hY d)
 
-@[irreducible]
-private def tensorEPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
+/-- The specified tensorEPullback construction used by the affine trace normal form.
+Source: blueprint sk-prop-an, Steps 5(b) and 6
+(blueprint: lem-amb-affine-trace-right-normal-form). -/
+@[irreducible]
+def tensorEPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
     (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) (a : ℤ) :
     (derivedTensorRight B Y (singleE B E Y d) ⋙ shiftFunctor _ a) ⋙
         (upperStar B f).leftDerivedFunctor ≅
@@ -136,8 +160,11 @@
     Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
       ((derivedTensorRightFunctor B X).mapIso (singleEPullback B N E c f hY d)) _)
 
-@[irreducible]
-private def lineENormalForm (X : Scheme.{u}) (hX : IsUnit (N : Γ(X, ⊤))) :
+/-- The specified lineENormalForm construction used by the affine trace normal form.
+Source: blueprint sk-prop-an, Steps 5(b) and 6
+(blueprint: lem-amb-affine-trace-right-normal-form). -/
+@[irreducible]
+def lineENormalForm (X : Scheme.{u}) (hX : IsUnit (N : Γ(X, ⊤))) :
     lineR B E X ≅ (upperStar B (AffineSpace PUnit.{u + 1} X ↘ X)).leftDerivedFunctor ⋙
       derivedTensorRight B (AffineSpace PUnit.{u + 1} X)
         (singleE B E (AffineSpace PUnit.{u + 1} X) 1) ⋙ shiftFunctor _ (2 : ℤ) := by
@@ -153,14 +180,20 @@
   (flat : ∀ X : Scheme.{u}, IsUnit (N : Γ(X, ⊤)) → ∀ d, ObjectProperty.flat (E X d))
   (prod : ∀ X : Scheme.{u}, IsUnit (N : Γ(X, ⊤)) → ∀ d, E X d ⊗ E X 1 ≅ E X (d + 1))
 
-@[irreducible]
-private def productE (X : Scheme.{u}) (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) :
+/-- The specified productE construction used by the affine trace normal form.
+Source: blueprint sk-prop-an, Steps 5(b) and 6
+(blueprint: lem-amb-affine-trace-right-normal-form). -/
+@[irreducible]
+def productE (X : Scheme.{u}) (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) :
     ((derivedTensor B X).obj (singleE B E X d)).obj (singleE B E X 1) ≅
       singleE B E X (d + 1) :=
   singleProductGeneral B X _ _ _ (flat X hX d) (prod X hX d)
 
-@[irreducible]
-private def towerENormalForm (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
+/-- The specified towerENormalForm construction used by the affine trace normal form.
+Source: blueprint sk-prop-an, Steps 5(b) and 6
+(blueprint: lem-amb-affine-trace-right-normal-form). -/
+@[irreducible]
+def towerENormalForm (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
     affineTraceRightTower (fun e ↦ lineR B E (affineTraceTower S e)) d ≅
       (upperStar B (affineTraceProjection S d)).leftDerivedFunctor ⋙
         derivedTensorRight B (affineTraceTower S d) (singleE B E (affineTraceTower S d) d) ⋙
```

### lean/Sheaf/Paper/EtaleProEtaleAdjunctionTransfer.lean

```diff
--- Old
+++ New
@@ -26,6 +26,7 @@
 
 @[expose] public noncomputable section
 set_option autoImplicit false
+set_option maxRecDepth 1000
 universe u
 open CategoryTheory CategoryTheory.Limits
 namespace AlgebraicGeometry.ProEtale.AdjunctionTransfer
@@ -299,73 +300,56 @@
   exact (proEtaleProperty_iff A T _).2
     (ProEtale.DerivedCategory.constructibleFiniteTor.shift ((proEtaleProperty_iff A T K).1 hK) n)
 
-/-- Transfer the etale adjunction with its prescribed counit, and identify it uniquely
-with the restriction of the Brown adjoint. The equivalence equalities ensure that the
-forward functors are the actual restricted comparison inverse images. The equation
-on cf identifies its inverse with the specified proper mate and open comparison,
-so cf is the canonical compact-support comparison for the same compactification. The localizing
-categories and compactification functor are expressed in the ordinary constant-ring
-presentation of the finite-discrete coefficient categories.
-
-Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-et-proet,
-det-sp-et-proet-adjunction-transfer, statement and both proof paragraphs
-(blueprint: det-sp-et-proet-adjunction-transfer).
-
-Proof:
-1. Put E_T = nu_T^*. For M',N' set M=Q_X M', N=Q_Y N'. Use the equivalence
-   counits, bounded-below full faithfulness (thm-weil-pbc-site-comparison), the etale
-   adjunction, and the given compact-support comparison to identify Hom(M',E_X G N)
-   with Hom(Rf_! M',N'). Naturality of the equivalence counits, etale adjunction and
-   compact-support comparison makes this a natural Hom equivalence.
-2. Transpose the identity to obtain the counit. It is c_f(G Q_Y N') inverse, followed
-   by E_Y(epsilon_et at Q_Y N'), followed by the equivalence counit at N'. At E_Y N,
-   the equivalence triangle identity gives the displayed formula using the inverse
-   equivalence unit at N. The Hom equivalence gives both adjunction triangle identities.
-3. The source comparison of finite-value and finite-stalk constructibility identifies
-   the generator property with the source's constructibleFiniteTor, so it is stable
-   under shifts. Given a Brown adjunction, transpose the transported small counit
-   to obtain a map from the small right-adjoint value to the Brown value. On Hom
-   from every shifted generator, this is the composite of the two adjunction
-   bijections. Its cone belongs to the localizing closure and is right orthogonal
-   to all shifted generators, hence zero: the left orthogonal of that right
-   orthogonal is localizing and contains the generators. Thus the comparison is
-   an isomorphism and Brown preserves the generators.
-4. Restrict the supplied Brown adjunction along the fully faithful inclusions.
-   Fullness of both inclusions retains exactly the Brown counit.
-5. det-sp-unique-right-adjoint transposes the two counits to mutually inverse natural
-   transformations. Injectivity of the Brown Hom equivalence proves uniqueness of
-   the counit-preserving isomorphism, with precisely the displayed ambient equation. -/
-theorem etaleProEtaleAdjunctionTransfer
-    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
-    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
-    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
-    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
-    [IsSeparated (X ↘ Spec (.of k))]
-    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
-    [IsSeparated (Y ↘ Spec (.of k))]
-    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
-    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
-    (_hA : ∃ n : ℕ, (ℓ ^ n : A) = 0) (c : Compactification f)
+/-- Transport a unique counit-preserving isomorphism along a specified source iso.
+Source: blueprint det-sp-et-proet-adjunction-transfer, uniqueness of right adjoints
+(blueprint: det-sp-et-proet-adjunction-transfer). -/
+theorem transportUniqueCounitIso
+    {C D E : Type*} [Category C] [Category D] [Category E]
+    (F : D ⥤ E) {G H J : C ⥤ D} {T : C ⥤ E}
+    (j : G ≅ H) (ε : G ⋙ F ⟶ T) (δ : J ⋙ F ⟶ T)
+    (h : ∃! γ : G ≅ J, ∀ K, F.map (γ.hom.app K) ≫ δ.app K = ε.app K) :
+    ∃! θ : H ≅ J, ∀ K,
+      F.map (θ.hom.app K) ≫ δ.app K = F.map (j.inv.app K) ≫ ε.app K := by
+  obtain ⟨γ, hγ, huniq⟩ := h
+  refine ⟨j.symm ≪≫ γ, ?_, ?_⟩
+  · intro K
+    change F.map (j.inv.app K ≫ γ.hom.app K) ≫ _ = _
+    rw [F.map_comp, Category.assoc, hγ]
+  · intro θ hθ
+    have hh : j ≪≫ θ = γ := by
+      apply huniq
+      intro K
+      change F.map (j.hom.app K ≫ θ.hom.app K) ≫ _ = _
+      rw [F.map_comp, Category.assoc, hθ, ← Category.assoc, ← F.map_comp,
+        j.hom_inv_id_app, F.map_id, Category.id_comp]
+    apply Iso.ext
+    apply NatTrans.ext
+    funext K
+    apply (cancel_epi (j.hom.app K)).1
+    simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
+      Iso.hom_inv_id_app_assoc] using congrArg (fun z ↦ z.hom.app K) hh
+
+/-- Transfer an adjunction across the specified comparison equivalences and comparison iso.
+The construction retains the quasi-inverse and actual counit, and restricts any Brown
+adjunction to the generator subcategories with its unique counit-preserving comparison.
+Source: blueprint det-sp-et-proet-adjunction-transfer, categorical proof paragraphs 1--3
+(blueprint: det-sp-et-proet-adjunction-transfer). -/
+theorem etaleProEtaleAdjunctionTransferOfComparison
+    (A : Type (u + 1)) [CommRing A] [Finite A]
+    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
     (hX : ∀ K, etaleProperty A X K → proEtaleProperty A X
       ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K))
     (hY : ∀ K, etaleProperty A Y K → proEtaleProperty A Y
       ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj K))
     (eX : (etaleProperty A X).FullSubcategory ≌ (proEtaleProperty A X).FullSubcategory)
     (eY : (etaleProperty A Y).FullSubcategory ≌ (proEtaleProperty A Y).FullSubcategory)
-    (heX : eX.functor = comparison A X hX) (heY : eY.functor = comparison A Y hY)
+    (_heX : eX.functor = comparison A X hX) (_heY : eY.functor = comparison A Y hY)
     (hEt : ∀ K, etaleProperty A X K → etaleProperty A Y
       ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K))
     (hPro : ∀ K, proEtaleProperty A X K → proEtaleProperty A Y
       ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K))
     (cf : etaleLowerShriek A c hEt ⋙ eY.functor ≅
       eX.functor ⋙ proEtaleLowerShriek A c hPro)
-    (_hcf : ∀ K : (etaleProperty A X).FullSubcategory,
-      (cf.inv.app K).hom =
-        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
-            (eqToHom (congrArg (fun F ↦ (F.obj K).obj) heX)) ≫
-          (compactSupportSiteComparison A c).hom.app ((etaleToPlus A X).obj K) ≫
-          eqToHom (congrArg (fun F ↦ (F.obj ((etaleLowerShriek A c hEt).obj K)).obj)
-            heY).symm)
     (G : (etaleProperty A Y).FullSubcategory ⥤ (etaleProperty A X).FullSubcategory)
     (adjEt : etaleLowerShriek A c hEt ⊣ G) :
     ∃ adjPro : proEtaleLowerShriek A c hPro ⊣ (eY.inverse ⋙ G ⋙ eX.functor),
@@ -476,4 +460,98 @@
       rw [hc]
       exact hγ N
 
+
+
+/-- Transfer the etale adjunction with its prescribed counit, and identify it uniquely
+with the restriction of the Brown adjoint. The equivalence equalities ensure that the
+forward functors are the actual restricted comparison inverse images. The equation
+on cf identifies its inverse with the specified proper mate and open comparison,
+so cf is the canonical compact-support comparison for the same compactification. The localizing
+categories and compactification functor are expressed in the ordinary constant-ring
+presentation of the finite-discrete coefficient categories.
+
+Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-et-proet,
+det-sp-et-proet-adjunction-transfer, statement and both proof paragraphs
+(blueprint: det-sp-et-proet-adjunction-transfer).
+
+Proof:
+1. Put E_T = nu_T^*. For M',N' set M=Q_X M', N=Q_Y N'. Use the equivalence
+   counits, bounded-below full faithfulness (thm-weil-pbc-site-comparison), the etale
+   adjunction, and the given compact-support comparison to identify Hom(M',E_X G N)
+   with Hom(Rf_! M',N'). Naturality of the equivalence counits, etale adjunction and
+   compact-support comparison makes this a natural Hom equivalence.
+2. Transpose the identity to obtain the counit. It is c_f(G Q_Y N') inverse, followed
+   by E_Y(epsilon_et at Q_Y N'), followed by the equivalence counit at N'. At E_Y N,
+   the equivalence triangle identity gives the displayed formula using the inverse
+   equivalence unit at N. The Hom equivalence gives both adjunction triangle identities.
+3. The source comparison of finite-value and finite-stalk constructibility identifies
+   the generator property with the source's constructibleFiniteTor, so it is stable
+   under shifts. Given a Brown adjunction, transpose the transported small counit
+   to obtain a map from the small right-adjoint value to the Brown value. On Hom
+   from every shifted generator, this is the composite of the two adjunction
+   bijections. Its cone belongs to the localizing closure and is right orthogonal
+   to all shifted generators, hence zero: the left orthogonal of that right
+   orthogonal is localizing and contains the generators. Thus the comparison is
+   an isomorphism and Brown preserves the generators.
+4. Restrict the supplied Brown adjunction along the fully faithful inclusions.
+   Fullness of both inclusions retains exactly the Brown counit.
+5. det-sp-unique-right-adjoint transposes the two counits to mutually inverse natural
+   transformations. Injectivity of the Brown Hom equivalence proves uniqueness of
+   the counit-preserving isomorphism, with precisely the displayed ambient equation. -/
+theorem etaleProEtaleAdjunctionTransfer
+    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
+    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
+    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
+    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
+    [IsSeparated (X ↘ Spec (.of k))]
+    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
+    [IsSeparated (Y ↘ Spec (.of k))]
+    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
+    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
+    (_hA : ∃ n : ℕ, (ℓ ^ n : A) = 0) (c : Compactification f)
+    (hX : ∀ K, etaleProperty A X K → proEtaleProperty A X
+      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K))
+    (hY : ∀ K, etaleProperty A Y K → proEtaleProperty A Y
+      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj K))
+    (eX : (etaleProperty A X).FullSubcategory ≌ (proEtaleProperty A X).FullSubcategory)
+    (eY : (etaleProperty A Y).FullSubcategory ≌ (proEtaleProperty A Y).FullSubcategory)
+    (heX : eX.functor = comparison A X hX) (heY : eY.functor = comparison A Y hY)
+    (hEt : ∀ K, etaleProperty A X K → etaleProperty A Y
+      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K))
+    (hPro : ∀ K, proEtaleProperty A X K → proEtaleProperty A Y
+      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K))
+    (cf : etaleLowerShriek A c hEt ⋙ eY.functor ≅
+      eX.functor ⋙ proEtaleLowerShriek A c hPro)
+    (_hcf : ∀ K : (etaleProperty A X).FullSubcategory,
+      (cf.inv.app K).hom =
+        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
+            (eqToHom (congrArg (fun F ↦ (F.obj K).obj) heX)) ≫
+          (compactSupportSiteComparison A c).hom.app ((etaleToPlus A X).obj K) ≫
+          eqToHom (congrArg (fun F ↦ (F.obj ((etaleLowerShriek A c hEt).obj K)).obj)
+            heY).symm)
+    (G : (etaleProperty A Y).FullSubcategory ⥤ (etaleProperty A X).FullSubcategory)
+    (adjEt : etaleLowerShriek A c hEt ⊣ G) :
+    ∃ adjPro : proEtaleLowerShriek A c hPro ⊣ (eY.inverse ⋙ G ⋙ eX.functor),
+      (∀ N : (etaleProperty A Y).FullSubcategory,
+        (adjPro.counit.app (eY.functor.obj N)) =
+          (proEtaleLowerShriek A c hPro).map
+              (eX.functor.map (G.map (eY.unitIso.inv.app N))) ≫
+            cf.inv.app (G.obj N) ≫ eY.functor.map (adjEt.counit.app N)) ∧
+      (∀ (hLoc : ∀ K, CategoryTheory.localizingClosure (proEtaleProperty A X) K →
+          CategoryTheory.localizingClosure (proEtaleProperty A Y)
+            ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K))
+        (J : (CategoryTheory.localizingClosure (proEtaleProperty A Y)).FullSubcategory ⥤
+          (CategoryTheory.localizingClosure (proEtaleProperty A X)).FullSubcategory)
+        (adjBrown : localizingLowerShriek A c hLoc ⊣ J),
+        ∃ hJ : ∀ N : (proEtaleProperty A Y).FullSubcategory,
+            proEtaleProperty A X ((J.obj ((toLocalizing A Y).obj N)).obj),
+          ∃! γ : (eY.inverse ⋙ G ⋙ eX.functor) ≅ brownRestriction A J hJ,
+            ∀ N : (proEtaleProperty A Y).FullSubcategory,
+              (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
+                  ((γ.hom.app N).hom) ≫
+                (adjBrown.counit.app ((toLocalizing A Y).obj N)).hom =
+              (adjPro.counit.app N).hom) := by
+  exact etaleProEtaleAdjunctionTransferOfComparison A c hX hY eX eY heX heY
+    hEt hPro cf G adjEt
+
 end AlgebraicGeometry.ProEtale.AdjunctionTransfer
```

The geometric comparison is obtained by whiskering the canonical chart iso
and the actual equivalence counit, then taking the explicit fully faithful
preimage through the full-subcategory inclusion. Thus its naturality is inherited
from these fixed maps, with no chosen isomorphism or added hypothesis.
