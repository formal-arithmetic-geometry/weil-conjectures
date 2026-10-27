# WeilConjectures.OrdinaryAutomorphismSquare.integralSquare and finiteSquare

## Reason

Kernel checking of the functor-category equality conversion repeatedly unfolds
large scheme-dependent operation categories. Construct the same composite componentwise in
`comparisonSquare`, with the operation family supplied as an argument. The
construction, its public signature and its component morphisms are unchanged.
A fully proved generic component calculation controls the unfolding.

## Old

```lean
def integralSquare (C : IntegralPullbackCompositionFamily l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (w : gX ≫ f = f ≫ gY)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    constructibleIntegralPullback l E f ⋙ constructibleIntegralPullback l E gX ≅
      constructibleIntegralPullback l E gY ⋙ constructibleIntegralPullback l E f :=
  (C gX f).symm ≪≫
    eqToIso (congrArg (fun h : X ⟶ Y ↦ constructibleIntegralPullback l E h) w) ≪≫ C f gY

```

## New

```lean
def comparisonSquare {A B : Type*} [Category A] [Category B]
    (P : ObjectProperty B) {I : Type*} (F : I → A ⥤ P.FullSubcategory)
    {i j : I} (w : i = j) {G H : A ⥤ P.FullSubcategory}
    (c : F i ≅ G) (d : F j ≅ H) : G ≅ H :=
  NatIso.ofComponents (fun K ↦
    (c.app K).symm ≪≫ P.isoMk
      (eqToIso (congrArg (fun t ↦ ((F t).obj K).obj) w)) ≪≫ d.app K)
    (by
      subst j
      intro K J r
      change G.map r ≫ (c.inv.app J ≫ 𝟙 _ ≫ d.hom.app J) =
        (c.inv.app K ≫ 𝟙 _ ≫ d.hom.app K) ≫ H.map r
      simpa only [Category.id_comp, Category.assoc, NatTrans.comp_app,
        Iso.trans_hom, Iso.symm_hom] using (c.symm ≪≫ d).hom.naturality r)

def integralSquare (C : IntegralPullbackCompositionFamily l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (w : gX ≫ f = f ≫ gY)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    constructibleIntegralPullback l E f ⋙ constructibleIntegralPullback l E gX ≅
      constructibleIntegralPullback l E gY ⋙ constructibleIntegralPullback l E f :=
  comparisonSquare (sfIntegralConstructible l E X)
    (fun h : X ⟶ Y ↦ constructibleIntegralPullback l E h)
    w (C gX f) (C f gY)

```

The fully proved private `comparisonSquare_eq` identifies this componentwise
construction with `c.symm ≪≫ eqToIso (congrArg F w) ≪≫ d`. Thus every component
and the natural isomorphism are unchanged. The same equation was previously
implemented by functor-category equality transport. No target statement changes
meaning; the target interpretation check sees the identical mathematical square.

The finite square has the identical performance repair. Its prior definition was:

```lean
def finiteSquare {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (w : gX ≫ f = f ≫ gY) (n : ℕ) :
    proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f ⋙
        proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) gX ≅
      proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) gY ⋙
        proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f :=
  (integralFiniteCanonicalPullbackComposition l E gX f n).symm ≪≫
    eqToIso (congrArg
      (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))) w) ≪≫
    integralFiniteCanonicalPullbackComposition l E f gY n

```

Its current definition and component constructor are:

```lean
def functorComparisonSquare {A B : Type*} [Category A] [Category B] {I : Type*}
    (F : I → A ⥤ B) {i j : I} (w : i = j) {G H : A ⥤ B}
    (c : F i ≅ G) (d : F j ≅ H) : G ≅ H :=
  NatIso.ofComponents
    (fun K ↦ (c.app K).symm ≪≫ eqToIso (congrArg (fun t ↦ (F t).obj K) w) ≪≫ d.app K)
    (by
      subst j
      intro K J r
      simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_hom, Iso.symm_hom,
        Iso.app_hom, Iso.app_inv, NatTrans.comp_app] using (c.symm ≪≫ d).hom.naturality r)

def finiteSquare {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (w : gX ≫ f = f ≫ gY) (n : ℕ) :
    proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f ⋙
        proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) gX ≅
      proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) gY ⋙
        proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f :=
  functorComparisonSquare
    (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))) w
    (integralFiniteCanonicalPullbackComposition l E gX f n)
    (integralFiniteCanonicalPullbackComposition l E f gY n)


```

`functorComparisonSquare_eq` proves equality of this componentwise construction
with the original functor-level composite. Its proof performs equality induction
in arbitrary categories, with no operation definition unfolded.

## Users

`tools/downstream.py Sheaf.Paper.FrobeniusPullbackOrdinaryExchange --uses integralSquare`
reports zero downstream modules and the item itself as the sole user. The same
`tools/downstream.py ... --uses finiteSquare` scan reports zero downstream modules
and this item's two references.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FrobeniusPullbackOrdinaryExchange | N2 | Component proof uses the componentwise construction; public signatures unchanged. |

The DAG parents remain attached; none is withdrawn. No target signature changes.

## Status

landed 20261025T123418-L-1868900 2026-10-25 (merge of deliver/N2/Sheaf.Paper.FrobeniusPullbackOrdinaryExchange)
