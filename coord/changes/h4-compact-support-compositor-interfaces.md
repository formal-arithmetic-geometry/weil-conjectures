# AlgebraicGeometry.ProEtale.coherenceProEtaleCompositor

## Reason

Checking the concrete composition square unfolded complete derived functors through
localization, colimit cocones and chosen compactifications, exceeding the 60-second
limit. In particular, projecting the chosen compositor after specializing compactification
instances caused the kernel to normalize this data before identifying the proof arguments.

Use named functors and component isomorphisms with explicit object endpoints. Retain
the independent four etale and six pro-etale factors in `CoherencePastingData`; it contains
no commutativity hypothesis. Its private `coherent` theorem proves the categorical pasting
calculation from the five constituent squares and the source-boundary factorization.
`coherenceCompositionDataOfChoice` keeps compactification instances abstract through
that proof. `coherenceCompositionData` specializes exactly the original choices from
c, d and e afterward. The complete file compiles without warnings in 27.3 seconds.

These are representation changes to the same canonical maps:

- `coherenceEtaleCompositor` keeps its signature verbatim (reviewer correction,
  2026-10-21: the `lean.statement` of def-pur-chosen-compactification-compositors records
  it); only its body is the componentwise form `coherenceCompositorOfChanges` of the same
  four factors.

- `coherenceEtaleFunctor`, `coherenceProEtaleFunctor`, `coherenceSiteFunctor` and
  `coherenceBoundedSiteFunctor` are named wrappers of the existing functors.
- `coherenceBoundaryIso` is exactly `compactExchangeTransportComparison`; the component
  wrappers evaluate existing isomorphisms and expose their object endpoints.
- The four etale factors remain the first compactification change, the second change,
  the original chosen etale compositor, and the output change. `coherenceIsoFour` writes
  their hom and inverse explicitly; its two named cancellation theorems are proved.
- The six pro-etale factors remain the proper-transport change for c, the inverse B_f,
  the proper-transport change for d, B_f, the chosen origin compositor, and the output
  change. The fifth factor is evaluated as `originCompositionModel`: the already-proved
  private `originComposition_model` theorem identifies it with the included original
  `originComposition`. The proof imports that private equation with `import all`.
- `CompactSupportSiteDiagram.etaleMap` evaluates the same four canonical factors via
  `coherenceEtaleCompositorComponent`. All other diagram generators are unchanged.
- Boundary records and endpoint types use the named wrappers, definitionally equal to
  their old functor expressions. No constructor assumes its comparison square.

The theorem signature, all original public imports, the unit route, and the geometric
hypotheses stay verbatim. No target is weakened. Because definitions used by the theorem
are represented differently, the independent reader should reopen its meaning review
and check the factor identification above. No source-library module changes.

## Old

The following are the changed existing definitions, verbatim from the current source.

```lean
def coherenceEtaleCompositor {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g)) :
    Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c ⋙
        Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d ≅
      Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) e :=
  letI := c.hasCompactification
  letI := d.hasCompactification
  letI := e.hasCompactification
  Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c
        (HasCompactification.compactification f))
      (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d) ≪≫
    Functor.isoWhiskerLeft (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f)
      (Etale.rightDerivedLowerShriekOfCompactificationPlusIso A d
        (HasCompactification.compactification g)) ≪≫
    Etale.rightDerivedLowerShriekPlusCompIso A f g ≪≫
    Etale.rightDerivedLowerShriekOfCompactificationPlusIso A
      (HasCompactification.compactification (f ≫ g)) e
```

```lean
def coherenceCompactificationChange {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (properTransportRefinement A (Compactification.infFst c d) L).symm ≪≫
    properTransportRefinement A (Compactification.infSnd c d) L
```

```lean
def coherenceProEtaleCompositor {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj)) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) e).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj) :=
  letI := c.hasCompactification
  letI := d.hasCompactification
  letI := e.hasCompactification
  let cf := HasCompactification.compactification f
  let dg := HasCompactification.compactification g
  let egf := HasCompactification.compactification (f ≫ g)
  let Fd := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d
  let Fdg := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) dg
  let Bf := (compactExchangeTransportComparison A cf).app L
  (Fd.mapIso (coherenceCompactificationChange A c cf L) ≪≫
    Fd.mapIso Bf.symm ≪≫
    coherenceCompactificationChange A d dg
      ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj L) ≪≫
    Fdg.mapIso Bf ≪≫
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι.mapIso
      ((originComposition A f g).app
        ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L)) ≪≫
    coherenceCompactificationChange A egf e L).hom
```

```lean
def coherenceCompositionSource {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (c : Compactification f) (d : Compactification g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (compactExchangeTransportComparison A d).app
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj L) ≪≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).mapIso
      ((compactExchangeTransportComparison A c).app L)
```

```lean
structure CompactSupportSiteBoundary (T : Scheme.{u}) where
  etale : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
  proEtale : _root_.DerivedCategory
    (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
  comparison :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj etale.obj ≅ proEtale
```

```lean
def coherenceCompactificationBoundary {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    CompactSupportSiteBoundary A Y where
  etale := (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj L
  proEtale := (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj)
  comparison := (compactExchangeTransportComparison A c).app L
```

```lean
def coherenceCompositionBoundary {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (c : Compactification f) (d : Compactification g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    CompactSupportSiteBoundary A Z where
  etale := (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d).obj
    ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj L)
  proEtale := (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).obj
    ((coherenceCompactificationBoundary A c L).proEtale)
  comparison := coherenceCompositionSource A c d L
```

```lean
def coherenceRestrictionTarget {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {u' : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback u' f' f v) (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    CompactSupportSiteBoundary A Y' where
  etale := (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
    (c.ofIsPullback sq)).obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) u').mapDerivedCategoryPlus.obj L)
  proEtale := (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (c.ofIsPullback sq)).obj
      ((upperStar (ModuleCat.{u + 1} A) u').leftDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj))
  comparison := (compactExchangeTransportTarget A sq c).app L
```

```lean
def coherencePushBoundary {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : CompactSupportSiteBoundary A X) : CompactSupportSiteBoundary A Y where
  etale := (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj
    b.etale
  proEtale := (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj b.proEtale
  comparison := (compactExchangeTransportComparison A c).app b.etale ≪≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).mapIso b.comparison
```

```lean
def CompactSupportSiteDiagram.etaleMap {P : WeilConjectures.PurityFiniteSetting.{u}}
    {T : Scheme.{u}} {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient T}
    (D : CompactSupportSiteDiagram P b₀ b₁) : b₀.etale ⟶ b₁.etale :=
  match D with
  | @CompactSupportSiteDiagram.refinement .(P) _ _ _ _ _ _ _ _ _ _ _ _ r L =>
      (Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso P.Coefficient r).inv.app L
  | @CompactSupportSiteDiagram.composition .(P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c d e L =>
      (coherenceEtaleCompositor P.Coefficient c d e).hom.app L
  | @CompactSupportSiteDiagram.restriction .(P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sq c L =>
      (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap P.Coefficient sq c).app L
  | @CompactSupportSiteDiagram.identity .(P) _ b => 𝟙 b.etale
  | @CompactSupportSiteDiagram.comp .(P) _ _ _ _ D E => D.etaleMap ≫ E.etaleMap
  | @CompactSupportSiteDiagram.push .(P) _ _ _ _ _ _ _ _ _ _ c _ _ D =>
      (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} P.Coefficient)
        c).map D.etaleMap
  | @CompactSupportSiteDiagram.pull .(P) _ _ _ _ _ _ v _ _ _ D =>
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v.left).mapDerivedCategoryPlus.map
        D.etaleMap
  | @CompactSupportSiteDiagram.change .(P) _ _ _ _ _ e₀ e₁ _ _ _ _ D =>
      e₀.inv ≫ D.etaleMap ≫ e₁.hom
```

## New

Replacement definitions, followed by the added public implementation API.

```lean
def coherenceEtaleCompositor {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g)) :
    Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c ⋙
        Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d ≅
      Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) e :=
  letI := c.hasCompactification
  letI := d.hasCompactification
  letI := e.hasCompactification
  coherenceCompositorOfChanges
    (coherenceEtaleFunctor A c)
    (coherenceEtaleFunctor A (HasCompactification.compactification f))
    (coherenceEtaleFunctor A d)
    (coherenceEtaleFunctor A (HasCompactification.compactification g))
    (coherenceEtaleFunctor A (HasCompactification.compactification (f ≫ g)))
    (coherenceEtaleFunctor A e)
    (coherenceEtaleChangeIso A c (HasCompactification.compactification f))
    (coherenceEtaleChangeIso A d (HasCompactification.compactification g))
    (coherenceChosenEtaleCompositorIso A f g)
    (coherenceEtaleChangeIso A (HasCompactification.compactification (f ≫ g)) e)
```

```lean
def coherenceCompactificationChange {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceProEtaleFunctor A c).obj
        ((coherenceBoundedSiteFunctor A X).obj L) ≅
      (coherenceProEtaleFunctor A d).obj
        ((coherenceBoundedSiteFunctor A X).obj L) :=
  (properTransportRefinement A (Compactification.infFst c d) L).symm ≪≫
    properTransportRefinement A (Compactification.infSnd c d) L
```

```lean
def coherenceProEtaleCompositor {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceProEtaleFunctor A d).obj
        ((coherenceProEtaleFunctor A c).obj
          ((coherenceBoundedSiteFunctor A X).obj L)) ⟶
      (coherenceProEtaleFunctor A e).obj
        ((coherenceBoundedSiteFunctor A X).obj L) :=
  (coherenceCompositionData A c d e L).proMap
```

```lean
def coherenceCompositionSource {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (c : Compactification f) (d : Compactification g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceBoundedSiteFunctor A Z).obj
        ((coherenceEtaleFunctor A d).obj ((coherenceEtaleFunctor A c).obj L)) ≅
      (coherenceProEtaleFunctor A d).obj
        ((coherenceProEtaleFunctor A c).obj
          ((coherenceBoundedSiteFunctor A X).obj L)) :=
  coherenceBoundaryComponent A d ((coherenceEtaleFunctor A c).obj L) ≪≫
    (coherenceProEtaleFunctor A d).mapIso
      (coherenceBoundaryComponent A c L)
```

```lean
structure CompactSupportSiteBoundary (T : Scheme.{u}) where
  etale : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
  proEtale : _root_.DerivedCategory
    (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
  comparison :
    (coherenceBoundedSiteFunctor A T).obj etale ≅ proEtale
```

```lean
def coherenceCompactificationBoundary {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    CompactSupportSiteBoundary A Y where
  etale := (coherenceEtaleFunctor A c).obj L
  proEtale := (coherenceProEtaleFunctor A c).obj
    ((coherenceBoundedSiteFunctor A X).obj L)
  comparison := coherenceBoundaryComponent A c L
```

```lean
def coherenceCompositionBoundary {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (c : Compactification f) (d : Compactification g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    CompactSupportSiteBoundary A Z where
  etale := (coherenceEtaleFunctor A d).obj
    ((coherenceEtaleFunctor A c).obj L)
  proEtale := (coherenceProEtaleFunctor A d).obj
    ((coherenceCompactificationBoundary A c L).proEtale)
  comparison := coherenceCompositionSource A c d L
```

```lean
def coherenceRestrictionTarget {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {u' : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback u' f' f v) (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    CompactSupportSiteBoundary A Y' where
  etale := (coherenceEtaleFunctor A
    (c.ofIsPullback sq)).obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) u').mapDerivedCategoryPlus.obj L)
  proEtale := (coherenceProEtaleFunctor A
    (c.ofIsPullback sq)).obj
      ((upperStar (ModuleCat.{u + 1} A) u').leftDerivedFunctor.obj
        ((coherenceBoundedSiteFunctor A X).obj L))
  comparison := (compactExchangeTransportTarget A sq c).app L
```

```lean
def coherencePushBoundary {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : CompactSupportSiteBoundary A X) : CompactSupportSiteBoundary A Y where
  etale := (coherenceEtaleFunctor A c).obj
    b.etale
  proEtale := (coherenceProEtaleFunctor A c).obj b.proEtale
  comparison := (coherenceBoundaryIso A c).app b.etale ≪≫
    (coherenceProEtaleFunctor A c).mapIso b.comparison
```

```lean
def CompactSupportSiteDiagram.etaleMap {P : WeilConjectures.PurityFiniteSetting.{u}}
    {T : Scheme.{u}} {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient T}
    (D : CompactSupportSiteDiagram P b₀ b₁) : b₀.etale ⟶ b₁.etale :=
  match D with
  | @CompactSupportSiteDiagram.refinement .(P) _ _ _ _ _ _ _ _ _ _ _ _ r L =>
      (Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso P.Coefficient r).inv.app L
  | @CompactSupportSiteDiagram.composition .(P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c d e L =>
      (coherenceEtaleCompositorComponent P.Coefficient c d e L).hom
  | @CompactSupportSiteDiagram.restriction .(P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sq c L =>
      (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap P.Coefficient sq c).app L
  | @CompactSupportSiteDiagram.identity .(P) _ b => 𝟙 b.etale
  | @CompactSupportSiteDiagram.comp .(P) _ _ _ _ D E => D.etaleMap ≫ E.etaleMap
  | @CompactSupportSiteDiagram.push .(P) _ _ _ _ _ _ _ _ _ _ c _ _ D =>
      (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} P.Coefficient)
        c).map D.etaleMap
  | @CompactSupportSiteDiagram.pull .(P) _ _ _ _ _ _ v _ _ _ D =>
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v.left).mapDerivedCategoryPlus.map
        D.etaleMap
  | @CompactSupportSiteDiagram.change .(P) _ _ _ _ _ e₀ e₁ _ _ _ _ D =>
      e₀.inv ≫ D.etaleMap ≫ e₁.hom
```

```lean
def coherenceFourMap {C : Type*} [Category* C] {a b c d e : C}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) : a ⟶ e :=
  f ≫ g ≫ h ≫ i
```

```lean
def coherenceSixMap {C : Type*} [Category* C] {a b c d e f g : C}
    (i : a ⟶ b) (j : b ⟶ c) (k : c ⟶ d) (l : d ⟶ e) (m : e ⟶ f) (n : f ⟶ g) :
    a ⟶ g := i ≫ j ≫ k ≫ l ≫ m ≫ n
```

```lean
theorem coherenceFourMap_hom_inv {C : Type*} [Category* C] {a b c d e : C}
    (i : a ≅ b) (j : b ≅ c) (k : c ≅ d) (l : d ≅ e) :
    coherenceFourMap i.hom j.hom k.hom l.hom ≫
        (l.inv ≫ k.inv ≫ j.inv ≫ i.inv) = 𝟙 a := by
  simp [coherenceFourMap, Category.assoc]
```

```lean
theorem coherenceFourMap_inv_hom {C : Type*} [Category* C] {a b c d e : C}
    (i : a ≅ b) (j : b ≅ c) (k : c ≅ d) (l : d ≅ e) :
    (l.inv ≫ k.inv ≫ j.inv ≫ i.inv) ≫
        coherenceFourMap i.hom j.hom k.hom l.hom = 𝟙 e := by
  simp [coherenceFourMap, Category.assoc]
```

```lean
def coherenceIsoFour {C : Type*} [Category* C] {a b c d e : C}
    (i : a ≅ b) (j : b ≅ c) (k : c ≅ d) (l : d ≅ e) : a ≅ e where
  hom := coherenceFourMap i.hom j.hom k.hom l.hom
  inv := l.inv ≫ k.inv ≫ j.inv ≫ i.inv
  hom_inv_id := coherenceFourMap_hom_inv i j k l
  inv_hom_id := coherenceFourMap_inv_hom i j k l
```

```lean
structure CoherencePastingData {C D : Type*} [Category* C] [Category* D] (N : C ⥤ D)
    (a₀ a₁ a₂ a₃ a₄ : C) (b₀ b₁ b₂ v₀ v₁ v₂ p q : D)
    (bin : N.obj a₀ ⟶ v₀) (bout : N.obj a₄ ⟶ q) where
  e₀ : a₀ ≅ a₁
  e₁ : a₁ ≅ a₂
  e₂ : a₂ ≅ a₃
  e₃ : a₃ ≅ a₄
  s₀ : N.obj a₀ ⟶ b₀
  s₁ : N.obj a₁ ⟶ b₁
  s₂ : N.obj a₂ ⟶ b₂
  s₃ : N.obj a₃ ⟶ p
  r₀ : b₀ ⟶ v₀
  r₁ : v₀ ⟶ v₁
  r₂ : v₁ ⟶ b₁
  rd : b₁ ⟶ b₂
  rb : b₂ ⟶ v₂
  o : v₂ ⟶ p
  re : p ⟶ q
  n : b₀ ⟶ b₁
```

```lean
def CoherencePastingData.etaleIso {C D : Type*} [Category* C] [Category* D] {N : C ⥤ D}
    {a₀ a₁ a₂ a₃ a₄ : C} {b₀ b₁ b₂ v₀ v₁ v₂ p q : D}
    {bin : N.obj a₀ ⟶ v₀} {bout : N.obj a₄ ⟶ q}
    (t : CoherencePastingData N a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ v₀ v₁ v₂ p q bin bout) : a₀ ≅ a₄ :=
  coherenceIsoFour t.e₀ t.e₁ t.e₂ t.e₃
```

```lean
def CoherencePastingData.proMap {C D : Type*} [Category* C] [Category* D] {N : C ⥤ D}
    {a₀ a₁ a₂ a₃ a₄ : C} {b₀ b₁ b₂ v₀ v₁ v₂ p q : D}
    {bin : N.obj a₀ ⟶ v₀} {bout : N.obj a₄ ⟶ q}
    (t : CoherencePastingData N a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ v₀ v₁ v₂ p q bin bout) : v₀ ⟶ q :=
  coherenceSixMap t.r₁ t.r₂ t.rd t.rb t.o t.re
```

```lean
def coherenceEvaluateCompositor {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (a : F ⋙ G ≅ H) (L : C) :
    G.obj (F.obj L) ≅ H.obj L := a.app L
```

```lean
def coherenceEvaluateSquare {C D E B : Type*}
    [Category* C] [Category* D] [Category* E] [Category* B]
    (F : C ⥤ D) (N : D ⥤ B) (M : C ⥤ E) (G : E ⥤ B)
    (a : F ⋙ N ≅ M ⋙ G) (L : C) : N.obj (F.obj L) ≅ G.obj (M.obj L) := a.app L
```

```lean
theorem coherenceEvaluateSquare_naturality {C D E B : Type*}
    [Category* C] [Category* D] [Category* E] [Category* B]
    (F : C ⥤ D) (N : D ⥤ B) (M : C ⥤ E) (G : E ⥤ B)
    (a : F ⋙ N ≅ M ⋙ G) {L K : C} (t : L ⟶ K) :
    N.map (F.map t) ≫ (coherenceEvaluateSquare F N M G a K).hom =
      (coherenceEvaluateSquare F N M G a L).hom ≫ G.map (M.map t) :=
  a.hom.naturality t
```

```lean
def coherenceEvaluateTriple {C D E B : Type*}
    [Category* C] [Category* D] [Category* E] [Category* B]
    (N : C ⥤ D) (F : D ⥤ E) (G : E ⥤ B) (H : D ⥤ B)
    (a : N ⋙ F ⋙ G ≅ N ⋙ H) (L : C) :
    G.obj (F.obj (N.obj L)) ≅ H.obj (N.obj L) := a.app L
```

```lean
theorem coherenceCompositorOfChanges_naturality
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F F' : C ⥤ D) (G G' : D ⥤ E) (H H' : C ⥤ E)
    (a : F ≅ F') (b : G ≅ G') (c : F' ⋙ G' ≅ H) (d : H ≅ H')
    {L M : C} (t : L ⟶ M) :
    G.map (F.map t) ≫
        (G.map (a.hom.app M) ≫ b.hom.app (F'.obj M) ≫ c.hom.app M ≫ d.hom.app M) =
      (G.map (a.hom.app L) ≫ b.hom.app (F'.obj L) ≫ c.hom.app L ≫ d.hom.app L) ≫
        H'.map t := by
  simp only [Category.assoc]
  rw [← G.map_comp_assoc, a.hom.naturality, G.map_comp_assoc,
    b.hom.naturality_assoc]
  have hc := c.hom.naturality_assoc t (d.hom.app M)
  dsimp only [Functor.comp_map] at hc
  rw [hc, d.hom.naturality]
```

```lean
def coherenceCompositorOfChanges
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F F' : C ⥤ D) (G G' : D ⥤ E) (H H' : C ⥤ E)
    (a : F ≅ F') (b : G ≅ G') (c : F' ⋙ G' ≅ H) (d : H ≅ H') :
    F ⋙ G ≅ H' :=
  NatIso.ofComponents
    (fun L ↦ coherenceIsoFour (G.mapIso (a.app L))
      (b.app (F'.obj L)) (c.app L) (d.app L))
    (fun t ↦ coherenceCompositorOfChanges_naturality F F' G G' H H' a b c d t)
```

```lean
def coherenceSiteFunctor (X : Scheme.{u}) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
```

```lean
def coherenceBoundedSiteFunctor (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  DerivedCategory.Plus.ι ⋙ coherenceSiteFunctor A X
```

```lean
def coherenceEtaleFunctor {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c
```

```lean
def coherenceProEtaleFunctor {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
```

```lean
def coherenceBoundaryIso {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    coherenceEtaleFunctor A c ⋙ coherenceBoundedSiteFunctor A Y ≅
      coherenceBoundedSiteFunctor A X ⋙ coherenceProEtaleFunctor A c :=
  compactExchangeTransportComparison A c
```

```lean
def coherenceBoundaryComponent {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceBoundedSiteFunctor A Y).obj ((coherenceEtaleFunctor A c).obj L) ≅
      (coherenceProEtaleFunctor A c).obj ((coherenceBoundedSiteFunctor A X).obj L) :=
  coherenceEvaluateSquare (coherenceEtaleFunctor A c) (coherenceBoundedSiteFunctor A Y)
    (coherenceBoundedSiteFunctor A X) (coherenceProEtaleFunctor A c)
    (coherenceBoundaryIso A c) L
```

```lean
def coherenceEtaleChangeIso {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) : coherenceEtaleFunctor A c ≅ coherenceEtaleFunctor A d :=
  Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c d
```

```lean
def coherenceChosenEtaleCompositorIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] :
    coherenceEtaleFunctor A
        (HasCompactification.compactification f) ⋙
      coherenceEtaleFunctor A
        (HasCompactification.compactification g) ≅
      coherenceEtaleFunctor A
        (HasCompactification.compactification (f ≫ g)) :=
  Etale.rightDerivedLowerShriekPlusCompIso A f g
```

```lean
def coherenceChosenProEtaleCompositorIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] :
    coherenceBoundedSiteFunctor A X ⋙
          coherenceProEtaleFunctor A
            (HasCompactification.compactification f) ⋙
          coherenceProEtaleFunctor A
            (HasCompactification.compactification g) ≅
      coherenceBoundedSiteFunctor A X ⋙
          coherenceProEtaleFunctor A
            (HasCompactification.compactification (f ≫ g)) :=
  originCompositionModel A f g
```

```lean
def coherenceChosenEtaleCompositorComponent {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceEtaleFunctor A (HasCompactification.compactification g)).obj
        ((coherenceEtaleFunctor A (HasCompactification.compactification f)).obj L) ≅
      (coherenceEtaleFunctor A (HasCompactification.compactification (f ≫ g))).obj L :=
  coherenceEvaluateCompositor
    (coherenceEtaleFunctor A (HasCompactification.compactification f))
    (coherenceEtaleFunctor A (HasCompactification.compactification g))
    (coherenceEtaleFunctor A (HasCompactification.compactification (f ≫ g)))
    (coherenceChosenEtaleCompositorIso A f g) L
```

```lean
def coherenceChosenProEtaleCompositorComponent {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceProEtaleFunctor A (HasCompactification.compactification g)).obj
        ((coherenceProEtaleFunctor A (HasCompactification.compactification f)).obj
          ((coherenceBoundedSiteFunctor A X).obj L)) ≅
      (coherenceProEtaleFunctor A (HasCompactification.compactification (f ≫ g))).obj
        ((coherenceBoundedSiteFunctor A X).obj L) :=
  coherenceEvaluateTriple (coherenceBoundedSiteFunctor A X)
    (coherenceProEtaleFunctor A (HasCompactification.compactification f))
    (coherenceProEtaleFunctor A (HasCompactification.compactification g))
    (coherenceProEtaleFunctor A (HasCompactification.compactification (f ≫ g)))
    (coherenceChosenProEtaleCompositorIso A f g) L
```

```lean
def coherenceCompositionDataOfChoice {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
  let cf := HasCompactification.compactification f
  let dg := HasCompactification.compactification g
  let egf := HasCompactification.compactification (f ≫ g)
  let NX := coherenceBoundedSiteFunctor A X
  let NY := coherenceBoundedSiteFunctor A Y
  let NZ := coherenceBoundedSiteFunctor A Z
  let Ec := coherenceEtaleFunctor A c
  let Ea := coherenceEtaleFunctor A cf
  let Ed := coherenceEtaleFunctor A d
  let Eb := coherenceEtaleFunctor A dg
  let Efg := coherenceEtaleFunctor A egf
  let Ee := coherenceEtaleFunctor A e
  let Fc := coherenceProEtaleFunctor A c
  let Fa := coherenceProEtaleFunctor A cf
  let Fd := coherenceProEtaleFunctor A d
  let Fb := coherenceProEtaleFunctor A dg
  let Ffg := coherenceProEtaleFunctor A egf
  let Fe := coherenceProEtaleFunctor A e
  let M := Ea.obj L
  CoherencePastingData NZ (Ed.obj (Ec.obj L)) (Ed.obj M) (Eb.obj M) (Efg.obj L)
    (Ee.obj L) (Fd.obj (NY.obj (Ec.obj L))) (Fd.obj (NY.obj M)) (Fb.obj (NY.obj M))
    (Fd.obj (Fc.obj (NX.obj L))) (Fd.obj (Fa.obj (NX.obj L)))
    (Fb.obj (Fa.obj (NX.obj L))) (Ffg.obj (NX.obj L)) (Fe.obj (NX.obj L))
    (coherenceCompositionSource A c d L).hom (coherenceBoundaryComponent A e L).hom :=
  let cf := HasCompactification.compactification f
  let dg := HasCompactification.compactification g
  let egf := HasCompactification.compactification (f ≫ g)
  let NY := coherenceBoundedSiteFunctor A Y
  let Ec := coherenceEtaleFunctor A c
  let Ea := coherenceEtaleFunctor A cf
  let Ed := coherenceEtaleFunctor A d
  let Fd := coherenceProEtaleFunctor A d
  let Fb := coherenceProEtaleFunctor A dg
  let M := Ea.obj L
  { e₀ := Ed.mapIso ((coherenceEtaleChangeIso A c cf).app L)
    e₁ := (coherenceEtaleChangeIso A d dg).app M
    e₂ := coherenceChosenEtaleCompositorComponent A f g L
    e₃ := (coherenceEtaleChangeIso A egf e).app L
    s₀ := (coherenceBoundaryComponent A d (Ec.obj L)).hom
    s₁ := (coherenceBoundaryComponent A d M).hom
    s₂ := (coherenceBoundaryComponent A dg M).hom
    s₃ := (coherenceBoundaryComponent A egf L).hom
    r₀ := Fd.map (coherenceBoundaryComponent A c L).hom
    r₁ := Fd.map (coherenceCompactificationChange A c cf L).hom
    r₂ := Fd.map (coherenceBoundaryComponent A cf L).inv
    rd := (coherenceCompactificationChange A d dg M).hom
    rb := Fb.map (coherenceBoundaryComponent A cf L).hom
    o := (coherenceChosenProEtaleCompositorComponent A f g L).hom
    re := (coherenceCompactificationChange A egf e L).hom
    n := Fd.map (NY.map ((coherenceEtaleChangeIso A c cf).hom.app L)) }
```

```lean
def coherenceCompositionData {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
  letI := c.hasCompactification
  letI := d.hasCompactification
  letI := e.hasCompactification
  let cf := HasCompactification.compactification f
  let dg := HasCompactification.compactification g
  let egf := HasCompactification.compactification (f ≫ g)
  let NX := coherenceBoundedSiteFunctor A X
  let NY := coherenceBoundedSiteFunctor A Y
  let NZ := coherenceBoundedSiteFunctor A Z
  let Ec := coherenceEtaleFunctor A c
  let Ea := coherenceEtaleFunctor A cf
  let Ed := coherenceEtaleFunctor A d
  let Eb := coherenceEtaleFunctor A dg
  let Efg := coherenceEtaleFunctor A egf
  let Ee := coherenceEtaleFunctor A e
  let Fc := coherenceProEtaleFunctor A c
  let Fa := coherenceProEtaleFunctor A cf
  let Fd := coherenceProEtaleFunctor A d
  let Fb := coherenceProEtaleFunctor A dg
  let Ffg := coherenceProEtaleFunctor A egf
  let Fe := coherenceProEtaleFunctor A e
  let M := Ea.obj L
  CoherencePastingData NZ (Ed.obj (Ec.obj L)) (Ed.obj M) (Eb.obj M) (Efg.obj L)
    (Ee.obj L) (Fd.obj (NY.obj (Ec.obj L))) (Fd.obj (NY.obj M)) (Fb.obj (NY.obj M))
    (Fd.obj (Fc.obj (NX.obj L))) (Fd.obj (Fa.obj (NX.obj L)))
    (Fb.obj (Fa.obj (NX.obj L))) (Ffg.obj (NX.obj L)) (Fe.obj (NX.obj L))
    (coherenceCompositionSource A c d L).hom (coherenceBoundaryComponent A e L).hom :=
  letI := c.hasCompactification
  letI := d.hasCompactification
  letI := e.hasCompactification
  coherenceCompositionDataOfChoice A c d e L
```

```lean
def coherenceEtaleCompositorComponent {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceEtaleFunctor A d).obj ((coherenceEtaleFunctor A c).obj L) ≅
      (coherenceEtaleFunctor A e).obj L :=
  (coherenceCompositionData A c d e L).etaleIso
```

## Users

`tools/downstream.py Sheaf.Paper.CompactSupportSiteCoherence --uses
coherenceEtaleCompositor coherenceProEtaleCompositor` reports zero current transitive
Lean importers; both declarations are mentioned only in the item. No external consumer
requires adaptation. This is not a withdrawal: the item and its DAG attachment remain,
and its full theorem is proved. No assertion is made from the importer count about
unfinished DAG parents.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CompactSupportSiteCoherence` | H4 | Same canonical factors, explicit component interfaces; prove the full coherence theorem. |

## Status

landed 20261021T013343-L-2289028 2026-10-21 (merge of deliver/H4/Sheaf.Paper.CompactSupportSiteCoherence)
