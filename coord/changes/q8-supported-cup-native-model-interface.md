# supportedCupFunctoriality native model interface

## Reason

The native ModuleCat-sheaf operation definitions and the three law predicates were
in the same module as their all-laws theorem. Separating the genuinely independent
algebra and comparison obligations requires a common model module to avoid an
import cycle: both results use those definitions, and the original theorem imports
both results. The original module publicly reexports the model module, retaining
every public declaration name and each law field. This extraction is for the
proof dependency direction; the definitions are also factored to avoid repeatedly
checking the large Boolean derived-category conversions.

The selected site is constructed before its sheaf category, so for either Boolean
value the category is definitionally the original etale or pro-etale category.
Its category, abelian and derived-category instances are the existing canonical
instances. Named source/target objects share the same single/shift endpoints.
The exact Hom helpers are generic composites of the same maps; the named
connecting morphism is the original coefficient sequence single-delta.
Normalized inverse image and comparison merely factor those composites.
Kummer is realization of the same extension after the identity direct-image
unitor. Signed products use the already published structured normalized Tate
data; their characterizing unit, positive-power, duality, associativity and
symmetry laws are retained. No coefficient datum, cohomological degree, scheme
hypothesis, support, twist or target law is changed.

All definitions and predicates now live in
Sheaf.Paper.SupportedCupFunctorialityModels. The original module contains the
proved localization calculation and the unchanged all-laws theorem. The two
remaining obligations are explicitly separate results; this is a decomposition,
not a claim that the full theorem is proved without sorry dependencies.

## Old

```lean
abbrev functorialCupSheaves (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :=
  match pro with
  | false => Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
  | true => Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)
```

```lean
instance functorialCupCategory (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    Category.{u + 1} (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance
```

```lean
instance functorialCupAbelian (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    Abelian (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance
```

```lean
instance functorialCupHasDerived (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : HasDerivedCategory.{u + 1} (P.functorialCupSheaves pro X) := by
  cases pro <;> infer_instance
```

```lean
def functorialCupSingle (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :=
  @DerivedCategory.singleFunctor (P.functorialCupSheaves pro X) _ _
    (P.functorialCupHasDerived pro X) 0
```

```lean
abbrev FunctorialCupH (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) (a r : ℤ) :=
  (P.functorialCupSingle pro X).obj (P.functorialCupSource pro i) ⟶
    ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r))⟦a⟧
```

```lean
instance functorialCupMonoidal (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    MonoidalCategory (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance
```

```lean
instance functorialCupSymmetric (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    SymmetricCategory (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance
```

```lean
instance functorialCupClosed (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    MonoidalClosed (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance
```

```lean
instance functorialCupDerivedMonoidal (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : MonoidalCategory (P.FunctorialCupDerived pro X) := inferInstance
```

```lean
def functorialCupTwistProducts (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) : FunctorialCupTwistProducts A m hA :=
  Classical.choice ((Scheme.etaleFiniteTwistPullback A m hm hA).elim fun _ hr ↦
    hr.elim fun _ hc ↦ hc.elim fun p hp ↦
      ⟨{ product := p
         left_unit := hp.the project server.the project server.1
         right_unit := hp.the project server.the project server.2.1
         positive := hp.the project server.the project server.2.2.1
         associativity := hp.the project server.the project server.the project server
         symmetry := hp.the project server.the project server.the project server.1
         evaluation := hp.the project server.the project server.the project server.2.1 }⟩)
```

```lean
def functorialCupPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
    (a r : ℤ) (α : P.FunctorialCupH pro i a r) : P.FunctorialCupH pro j a r :=
  (P.functorialCupSingle pro Y).map (P.functorialCupExchange pro i j v g sq).inv ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).inv.app
      (P.functorialCupSource pro i) ≫
    (P.functorialCupInverseImage pro v).mapDerivedCategory.map α ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategory.commShiftIso a).hom.app
      ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r)) ≫
    (((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).hom.app
        (P.functorialCupTwist pro X r) ≫
      (P.functorialCupSingle pro Y).map (P.functorialCupTwistPullback pro v aX r).hom)⟦a⟧'
```

```lean
def functorialCupKummerExt (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (v : Γ(X, ⊤)ˣ) :
    Abelian.Ext (P.functorialCupConstant pro X) (P.functorialCupTwist pro X 1) 1 :=
  match pro with
  | false => functorialCupExtTarget (P.functorialCupFrameTwistEtale_eq X)
      (P.frameKummerEtale X aX v)
  | true => functorialCupExtTarget (P.functorialCupFrameTwist_eq X) (P.frameKummer X aX v)
```

```lean
def functorialCupKummer (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (v : Γ(X, ⊤)ˣ) :
    P.FunctorialCupH pro (𝟙 X) 1 1 :=
  (P.functorialCupSingle pro X).map (P.functorialCupFullSupportIso pro X).hom ≫
    functorialCupExtHom (hD := P.functorialCupHasDerived pro X)
      (P.functorialCupKummerExt pro X aX v)
```

```lean
abbrev FunctorialCupOrdinaryH (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) (a r : ℤ) :=
  (P.functorialCupSingle pro X).obj (P.functorialCupConstant pro X) ⟶
    ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r))⟦a⟧
```

```lean
def functorialCupOrdinaryPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ)
    (α : P.FunctorialCupOrdinaryH pro X a r) : P.FunctorialCupOrdinaryH pro Y a r :=
  (P.functorialCupSingle pro Y).map (P.functorialCupConstantPullback pro v).inv ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).inv.app
      (P.functorialCupConstant pro X) ≫
    (P.functorialCupInverseImage pro v).mapDerivedCategory.map α ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategory.commShiftIso a).hom.app
      ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r)) ≫
    (((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).hom.app
        (P.functorialCupTwist pro X r) ≫
      (P.functorialCupSingle pro Y).map (P.functorialCupTwistPullback pro v aX r).hom)⟦a⟧'
```

```lean
def functorialCupBoundary (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
    (α : P.FunctorialCupOpenH pro i a r) : P.FunctorialCupH pro i (a + 1) r :=
  ShiftedHom.comp (P.functorialCupSequence_shortExact pro i).singleδ α rfl
```

```lean
abbrev FunctorialCupOpenH (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ) :=
  (P.functorialCupSingle pro X).obj (P.functorialCupOpenSource pro i) ⟶
    ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r))⟦a⟧
```

```lean
def functorialCupOpenPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
    (a r : ℤ) (α : P.FunctorialCupOpenH pro i a r) : P.FunctorialCupOpenH pro j a r :=
  (P.functorialCupSingle pro Y).map
      (P.functorialCupOpenExchange_existsUnique pro i j v g sq).choose.inv ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).inv.app
      (P.functorialCupOpenSource pro i) ≫
    (P.functorialCupInverseImage pro v).mapDerivedCategory.map α ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategory.commShiftIso a).hom.app
      ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r)) ≫
    (((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).hom.app
        (P.functorialCupTwist pro X r) ≫
      (P.functorialCupSingle pro Y).map (P.functorialCupTwistPullback pro v aX r).hom)⟦a⟧'
```

```lean
def functorialCupCompare (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
    (α : P.FunctorialCupH false i a r) : P.FunctorialCupH true i a r :=
  (P.functorialCupSingle true X).map (P.functorialCupComparisonSource_existsUnique i).choose.inv ≫
    functorialCupExactHom (hB := P.functorialCupHasDerived false X)
      (hD := P.functorialCupHasDerived true X) (P.functorialCupComparisonFunctor X) a α ≫
    ((P.functorialCupSingle true X).map
      (eqToHom (P.functorialCupComparisonTwist_eq X r)))⟦a⟧'
```

```lean
def functorialCupOrdinaryCompare (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (a r : ℤ)
    (α : P.FunctorialCupOrdinaryH false X a r) : P.FunctorialCupOrdinaryH true X a r :=
  (P.functorialCupSingle true X).map
      (eqToHom (P.functorialCupComparisonConstant_eq X).symm) ≫
  functorialCupExactHom (hB := P.functorialCupHasDerived false X)
    (hD := P.functorialCupHasDerived true X) (P.functorialCupComparisonFunctor X) a α ≫
    ((P.functorialCupSingle true X).map
      (eqToHom (P.functorialCupComparisonTwist_eq X r)))⟦a⟧'
```

```lean
def functorialCupOpenCompare (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
    (α : P.FunctorialCupOpenH false i a r) : P.FunctorialCupOpenH true i a r :=
  (P.functorialCupSingle true X).map (P.functorialCupComparisonOpen_existsUnique i).choose.inv ≫
    functorialCupExactHom (hB := P.functorialCupHasDerived false X)
      (hD := P.functorialCupHasDerived true X) (P.functorialCupComparisonFunctor X) a α ≫
    ((P.functorialCupSingle true X).map
      (eqToHom (P.functorialCupComparisonTwist_eq X r)))⟦a⟧'
```

```lean
instance functorialCupGrothendieck (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance
```

```lean
instance functorialCupMonoidalPreadditive (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) :
    MonoidalPreadditive (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance
```

```lean
instance functorialCupFlatResolutions (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : Abelian.HasFunctorialFlatResolution (P.functorialCupSheaves pro X) := by
  cases pro <;> infer_instance
```

```lean
def functorialCupReindex (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) {a b r s : ℤ} (ha : a = b) (hr : r = s)
    (α : P.FunctorialCupH pro i a r) : P.FunctorialCupH pro i b s :=
  ha ▸ hr ▸ α
```

```lean
structure FunctorialCupLocalizationLaws (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop where
  full_support : ∀ (X : Scheme.{u}) (_aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ),
    Function.Bijective (P.functorialCupForget pro (𝟙 X) a r)
  forget_support : ∀ {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
      [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
      (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
      (a r : ℤ) (α : P.FunctorialCupH pro i a r),
    P.functorialCupForget pro j a r (P.functorialCupPullback pro i j v g sq aX a r α) =
      P.functorialCupOrdinaryPullback pro v aX a r (P.functorialCupForget pro i a r α)
  open_restriction : ∀ {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
      [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
      (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
      (a r : ℤ) (α : P.FunctorialCupOrdinaryH pro X a r),
    P.functorialCupOpenPullback pro i j v g sq aX a r
        (P.functorialCupOpenRestriction pro i a r α) =
      P.functorialCupOpenRestriction pro j a r
        (P.functorialCupOrdinaryPullback pro v aX a r α)
  boundary : ∀ {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
      [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
      (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
      (a r : ℤ) (α : P.FunctorialCupOpenH pro i a r),
    P.functorialCupPullback pro i j v g sq aX (a+1) r
        (P.functorialCupBoundary pro i a r α) =
      P.functorialCupBoundary pro j a r (P.functorialCupOpenPullback pro i j v g sq aX a r α)
```

## New

```lean
abbrev functorialCupSheaves (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :=
  Sheaf (functorialCupTopology pro X) (ModuleCat.{u + 1} P.Coefficient)
```

```lean
@[reducible] instance functorialCupCategory (P : PurityFiniteSetting.{u}) (pro : Bool) (X :
    Scheme.{u}) :
    Category.{u + 1} (P.functorialCupSheaves pro X) := inferInstance
```

```lean
@[reducible] instance functorialCupAbelian (P : PurityFiniteSetting.{u}) (pro : Bool) (X :
    Scheme.{u}) :
    Abelian (P.functorialCupSheaves pro X) := inferInstance
```

```lean
@[reducible] instance functorialCupHasDerived (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : HasDerivedCategory.{u + 1} (P.functorialCupSheaves pro X) :=
  inferInstance
```

```lean
def functorialCupSingle (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    P.functorialCupSheaves pro X ⥤ P.FunctorialCupDerived pro X :=
  @DerivedCategory.singleFunctor (P.functorialCupSheaves pro X) _ _
    (P.functorialCupHasDerived pro X) 0
```

```lean
abbrev FunctorialCupH (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) (a r : ℤ) : Type (u + 1) :=
  P.functorialCupSourceObject pro i ⟶
    P.functorialCupTarget pro X a r
```

```lean
@[reducible] instance functorialCupMonoidal (P : PurityFiniteSetting.{u}) (pro : Bool) (X :
    Scheme.{u}) :
    MonoidalCategory (P.functorialCupSheaves pro X) := by infer_instance
```

```lean
@[reducible] instance functorialCupSymmetric (P : PurityFiniteSetting.{u}) (pro : Bool) (X :
    Scheme.{u}) :
    SymmetricCategory (P.functorialCupSheaves pro X) := by infer_instance
```

```lean
@[reducible] instance functorialCupClosed (P : PurityFiniteSetting.{u}) (pro : Bool) (X :
    Scheme.{u}) :
    MonoidalClosed (P.functorialCupSheaves pro X) := by infer_instance
```

```lean
instance functorialCupDerivedMonoidal (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : MonoidalCategory (P.FunctorialCupDerived pro X) :=
  (functorialCupTensorData (B := P.functorialCupSheaves pro X)).1
```

```lean
def functorialCupTwistProducts (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) : FunctorialCupTwistProducts A m hA :=
  let t := Scheme.finiteEtaleTwistPullbackData A m hm hA
  { product := t.p
    left_unit := t.laws.the project server.the project server.1
    right_unit := t.laws.the project server.the project server.2.1
    positive := t.laws.the project server.the project server.2.2.1
    associativity := t.laws.the project server.the project server.the project server
    symmetry := t.laws.the project server.the project server.the project server.1
    evaluation := t.laws.the project server.the project server.the project server.2.1 }
```

```lean
def functorialCupPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
    (a r : ℤ) (α : P.FunctorialCupH pro i a r) : P.FunctorialCupH pro j a r :=
  functorialCupNormalizedHom (hB := P.functorialCupHasDerived pro X)
    (hD := P.functorialCupHasDerived pro Y) (P.functorialCupInverseImage pro v)
    (P.functorialCupExchange pro i j v g sq) (P.functorialCupTwistPullback pro v aX r) a α
```

```lean
def functorialCupKummerExt (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (v : Γ(X, ⊤)ˣ) :
    Abelian.Ext (P.functorialCupConstant pro X) (P.functorialCupTwist pro X 1) 1 :=
  match pro with
  | false => by
      letI : HasExt.{u + 1} (P.functorialCupSheaves false X) := P.functorialCupHasExt false X
      exact functorialCupExtTarget (P.functorialCupFrameTwistEtale_eq X)
        (P.frameKummerEtale X aX v)
  | true => by
      letI : HasExt.{u + 1} (P.functorialCupSheaves true X) := P.functorialCupHasExt true X
      exact functorialCupExtTarget (P.functorialCupFrameTwist_eq X) (P.frameKummer X aX v)
```

```lean
def functorialCupKummer (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (v : Γ(X, ⊤)ˣ) :
    P.FunctorialCupH pro (𝟙 X) 1 1 :=
  functorialCupSupportedExt (hD := P.functorialCupHasDerived pro X)
    (P.functorialCupFullSupportIso pro X) (P.functorialCupKummerExt pro X aX v)
```

```lean
abbrev FunctorialCupOrdinaryH (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) (a r : ℤ) : Type (u + 1) :=
  (P.functorialCupSingle pro X).obj (P.functorialCupConstant pro X) ⟶
    P.functorialCupTarget pro X a r
```

```lean
def functorialCupOrdinaryPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ)
    (α : P.FunctorialCupOrdinaryH pro X a r) : P.FunctorialCupOrdinaryH pro Y a r :=
  functorialCupNormalizedHom (hB := P.functorialCupHasDerived pro X)
    (hD := P.functorialCupHasDerived pro Y) (P.functorialCupInverseImage pro v)
    (P.functorialCupConstantPullback pro v) (P.functorialCupTwistPullback pro v aX r) a α
```

```lean
def functorialCupBoundary (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
    (α : P.FunctorialCupOpenH pro i a r) : P.FunctorialCupH pro i (a + 1) r :=
  ShiftedHom.comp (P.functorialCupConnecting pro i) α rfl
```

```lean
abbrev FunctorialCupOpenH (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ) : Type (u + 1) :=
  (P.functorialCupSingle pro X).obj (P.functorialCupOpenSource pro i) ⟶
    P.functorialCupTarget pro X a r
```

```lean
def functorialCupOpenPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
    (a r : ℤ) (α : P.FunctorialCupOpenH pro i a r) : P.FunctorialCupOpenH pro j a r :=
  functorialCupNormalizedHom (hB := P.functorialCupHasDerived pro X)
    (hD := P.functorialCupHasDerived pro Y) (P.functorialCupInverseImage pro v)
    (P.functorialCupOpenExchange_existsUnique pro i j v g sq).choose
    (P.functorialCupTwistPullback pro v aX r) a α
```

```lean
def functorialCupCompare (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
    (α : P.FunctorialCupH false i a r) : P.FunctorialCupH true i a r :=
  functorialCupNormalizedHom (hB := P.functorialCupHasDerived false X)
    (hD := P.functorialCupHasDerived true X) (P.functorialCupComparisonFunctor X)
    (P.functorialCupComparisonSource_existsUnique i).choose (eqToIso
    (P.functorialCupComparisonTwist_eq X r)) a α
```

```lean
def functorialCupOrdinaryCompare (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (a r : ℤ)
    (α : P.FunctorialCupOrdinaryH false X a r) : P.FunctorialCupOrdinaryH true X a r :=
  functorialCupNormalizedHom (hB := P.functorialCupHasDerived false X)
    (hD := P.functorialCupHasDerived true X) (P.functorialCupComparisonFunctor X)
    (eqToIso (P.functorialCupComparisonConstant_eq X)) (eqToIso
    (P.functorialCupComparisonTwist_eq X r)) a α
```

```lean
def functorialCupOpenCompare (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
    (α : P.FunctorialCupOpenH false i a r) : P.FunctorialCupOpenH true i a r :=
  functorialCupNormalizedHom (hB := P.functorialCupHasDerived false X)
    (hD := P.functorialCupHasDerived true X) (P.functorialCupComparisonFunctor X)
    (P.functorialCupComparisonOpen_existsUnique i).choose (eqToIso
    (P.functorialCupComparisonTwist_eq X r)) a α
```

The four localization fields are named propositions with the exact original
quantifiers and equations, so their record projections share these types.

The final localization record is:

```lean
structure FunctorialCupLocalizationLaws (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop where
  full_support : P.FunctorialCupLocalizationFullSupport pro
  forget_support : P.FunctorialCupLocalizationForgetSupport pro
  open_restriction : P.FunctorialCupLocalizationOpenRestriction pro
  boundary : P.FunctorialCupLocalizationBoundary pro
```

The new `functorialCupConnecting` is exactly
`(P.functorialCupSequence_shortExact pro i).singleδ`, with the original native
source and open-source endpoints. Naming it shares that connecting map in every
boundary expression. It neither selects a new map nor changes the boundary sign.
The four localization field types are given names (`FunctorialCupLocalizationFullSupport`,
`FunctorialCupLocalizationForgetSupport`, `FunctorialCupLocalizationOpenRestriction`,
`FunctorialCupLocalizationBoundary`); their expanded propositions are unchanged.

```lean
instance functorialCupGrothendieck (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (P.functorialCupSheaves pro X) := by infer_instance
```

```lean
instance functorialCupMonoidalPreadditive (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) :
    MonoidalPreadditive (P.functorialCupSheaves pro X) := by infer_instance
```

```lean
instance functorialCupFlatResolutions (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : Abelian.HasFunctorialFlatResolution (P.functorialCupSheaves pro X) := by
  infer_instance
```

```lean
def functorialCupReindex (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) {a b r s : ℤ} (ha : a = b) (hr : r = s)
    (α : P.FunctorialCupH pro i a r) : P.FunctorialCupH pro i b s :=
  α ≫ eqToHom (congrArg₂
    (fun r a ↦ P.functorialCupTarget pro X a r)
    hr ha)
```
The additional Grothendieck alias is the existing instance, named before the
single construction. Reindexing uses composition with `eqToHom` on the target;
transporting either reflexive equality is the identity. The normalized Hom and
boundary proofs form and cancel the short-complex isomorphism for abstract
abelian categories before specializing it. This changes only proof elaboration.

## Users

The following source users were checked textually with tools/downstream.py and
whole-declaration name searches. The public names and law field signatures are
retained through the public model import, and all changed composites are the
same canonical operations. No downstream module is adapted. A target statement
using the factored definitions needs the normal independent definition review.
The selected direct consumer checks for this interface are
Sheaf.Paper.ClosedSupportedCupVanishing and Sheaf.Paper.PurityDivisorClass.

| module | holder or disposition | effect |
| --- | --- | --- |
| Sheaf.Paper.SupportedCupFunctoriality | Q8 | same statement; localization proof and assembly |
| Sheaf.Paper.SupportedCupFunctorialityModels | new in this delivery | common operation interface |
| Sheaf.Paper.SupportedCupAlgebra | new in this delivery | native algebra obligation |
| Sheaf.Paper.SupportedCupNativeCoherence | new in this delivery | seven native coherence clauses |
| Sheaf.Paper.SupportedCupComparison | new in this delivery | comparison assembly |
| Sheaf.Paper.SupportedCupComparisonBasic | new in this delivery | five proved comparison clauses |
| Sheaf.Paper.SupportedCupComparisonCoherence | new in this delivery | six comparison clauses |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | unchanged; no adaptation | same named operations: `functorialCupSingle` |
| Sheaf.Paper.CartierClassAgreement | unchanged; no adaptation | same named operations: `FunctorialCupH`, `functorialCupPullback`, `functorialCupCompare` |
| Sheaf.Paper.CartierRelativeBoundaryRealization | unchanged; no adaptation | same named operations: `functorialCupCompare` |
| Sheaf.Paper.CartierRelativeKummerRealization | unchanged; no adaptation | same named operations: `functorialCupSheaves`, `functorialCupCategory`, `functorialCupAbelian`, `functorialCupHasDerived`, `functorialCupSingle`, `functorialCupPullback` |
| Sheaf.Paper.CartierSupportedComparisonSquare | unchanged; no adaptation | same named operations: `functorialCupSheaves`, `functorialCupCategory`, `functorialCupAbelian`, `functorialCupHasDerived`, `functorialCupSingle`, `functorialCupCompare` |
| Sheaf.Paper.ClosedSupportedCupVanishing | unchanged; no adaptation | same named operations: `functorialCupSingle`, `FunctorialCupH`, `FunctorialCupOrdinaryH`, `functorialCupOrdinaryPullback` |
| Sheaf.Paper.CompactProductTwistLaws | unchanged; no adaptation | same named operations: `FunctorialCupH`, `functorialCupCompare` |
| Sheaf.Paper.ComparisonImageClosedSectionNormalization | unchanged; no adaptation | same named operations: `functorialCupSheaves`, `functorialCupCategory`, `functorialCupAbelian`, `functorialCupHasDerived`, `functorialCupSingle` |
| Sheaf.Paper.CoordinateGermCohomologyClasses | unchanged; no adaptation | same named operations: `FunctorialCupH`, `functorialCupPullback` |
| Sheaf.Paper.CoordinateGermConcentrationData | unchanged; no adaptation | same named operations: `functorialCupHasDerived`, `functorialCupSingle`, `FunctorialCupH`, `functorialCupCompare` |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | unchanged; no adaptation | same named operations: `functorialCupSingle`, `FunctorialCupH`, `functorialCupCompare` |
| Sheaf.Paper.FlagLocalComparison | unchanged; no adaptation | same named operations: `FunctorialCupH`, `functorialCupPullback`, `functorialCupCompare` |
| Sheaf.Paper.FrameHomZariskiSeparated | unchanged; no adaptation | same named operations: `functorialCupPullback` |
| Sheaf.Paper.FrameProductPullback | unchanged; no adaptation | same named operations: `functorialCupPullback` |
| Sheaf.Paper.FramedEtaleHom | unchanged; no adaptation | same named operations: `FunctorialCupH` |
| Sheaf.Paper.FramedForgetSupport | unchanged; no adaptation | same named operations: `FunctorialCupOrdinaryH` |
| Sheaf.Paper.FramedProPredicate | unchanged; no adaptation | same named operations: `FunctorialCupH`, `functorialCupCompare` |
| Sheaf.Paper.FramedProRealization | unchanged; no adaptation | same named operations: `functorialCupCompare` |
| Sheaf.Paper.FramedRealizationProperty | unchanged; no adaptation | same named operations: `functorialCupOrdinaryCompare` |
| Sheaf.Paper.FramedRealizationPullback | unchanged; no adaptation | same named operations: `functorialCupPullback` |
| Sheaf.Paper.KummerProductShearHomotopy | unchanged; no adaptation | same named operations: `functorialCupPullback` |
| Sheaf.Paper.LineZeroClassEtaleRealization | unchanged; no adaptation | same named operations: `functorialCupSheaves`, `functorialCupCategory`, `functorialCupAbelian`, `functorialCupHasDerived`, `functorialCupSingle`, `functorialCupCompare` |
| Sheaf.Paper.LocalizedTopChern | unchanged; no adaptation | same named operations: `functorialCupSingle`, `FunctorialCupH`, `functorialCupPullback`, `FunctorialCupOrdinaryH` |
| Sheaf.Paper.NormalizedCartierForget | unchanged; no adaptation | same named operations: `FunctorialCupH`, `functorialCupCompare`, `functorialCupOrdinaryCompare` |
| Sheaf.Paper.NormalizedCartierLocalEquation | unchanged; no adaptation | same named operations: `FunctorialCupH`, `functorialCupPullback`, `functorialCupCompare` |
| Sheaf.Paper.NormalizedCartierSum | unchanged; no adaptation | same named operations: `FunctorialCupH`, `functorialCupCompare` |
| Sheaf.Paper.NormalizedDivisorFamilyPullback | unchanged; no adaptation | same named operations: `functorialCupPullback` |
| Sheaf.Paper.PurityDivisorClass | unchanged; no adaptation | same named operations: `functorialCupCategory`, `functorialCupAbelian`, `functorialCupHasDerived`, `FunctorialCupH`, `functorialCupPullback`, `functorialCupCompare`, `functorialCupOrdinaryCompare` |
| Sheaf.Paper.PurityExteriorProductFrame | unchanged; no adaptation | same named operations: `functorialCupSingle`, `FunctorialCupH`, `functorialCupPullback` |
| Sheaf.Paper.PurityFrameIndependence | unchanged; no adaptation | same named operations: `functorialCupPullback` |
| Sheaf.Paper.RegularImmersionClassData | unchanged; no adaptation | same named operations: `FunctorialCupH`, `functorialCupPullback` |
| Sheaf.Paper.SupportedClassGeometry | unchanged; no adaptation | same named operations: `functorialCupSingle`, `FunctorialCupH`, `functorialCupPullback` |
| Sheaf.Paper.SupportedClassSiteComparison | unchanged; no adaptation | same named operations: `functorialCupSingle` |
| Sheaf.Paper.SupportedExteriorClassArrows | unchanged; no adaptation | same named operations: `functorialCupSingle`, `FunctorialCupH` |
| Sheaf.Paper.SupportedExteriorClasses | unchanged; no adaptation | same named operations: `functorialCupSingle`, `FunctorialCupH` |
| Sheaf.Paper.VectorBundleThom | unchanged; no adaptation | same named operations: `functorialCupSingle` |
| Sheaf.Paper.VectorBundleThomClass | unchanged; no adaptation | same named operations: `functorialCupSingle`, `FunctorialCupH`, `functorialCupPullback` |
| Sheaf.Paper.VectorBundleThomMaps | unchanged; no adaptation | same named operations: `functorialCupSingle` |

## Status

landed 20261026T002320-L-75804 2026-10-26 (merge of deliver/Q8/Sheaf.Paper.SupportedCupFunctoriality)

The model also proves `normalizedKernelIso_of_exact` privately before native
instantiation. Both open-exchange existence proofs apply this generic lemma,
so conversion of the mapped short-complex projections is checked once in
abstract abelian categories. This changes no public signature or operation.

Consumer performance check: an unchanged `PurityDivisorClass` copy compiled
against the published baseline, without the sandbox overlay, also exceeded
the per-file limit (69 seconds). The packet-overlay run exceeded it at
84 seconds; profiling a second overlay run reported 72 seconds. Thus the
baseline already has a consumer performance failure. No consumer definition
or proof is changed in this delivery. `ClosedSupportedCupVanishing` compiled
unchanged against the packet.
