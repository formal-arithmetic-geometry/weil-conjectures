# Cartier reduction data and its normalized scalar-unit interfaces

## Reason

The comparison proof needs the already stated finite-coefficient Kummer theorem. That theorem imports SupportedCartierBoundaryExistence, whose proof originally imported the full comparison module for its first two existence theorems. Importing the coefficient theorem back into the comparison module creates a cycle. Factor the existing constructions and the now proved existence results into CartierReductionData; the original module publicly imports it. The boundary helper imports that foundation. This is a dependency-cycle refactoring, not a response to a file compile timeout. Every existing public declaration name and theorem signature remains available.

The scalar-adjunct proofs also repeatedly normalize the same geometric functor expressions. Named generic boundary/Kummer/composition expressions and the abstract DerivedExtUnit predicate keep the argument at the categorical interface. They are definitionally the previous expressions. Eight proved Prop-valued sheafification/HasExt instance witnesses cache the same instances; proof irrelevance preserves all data. The integral constant comparison is the exact former subexpression factored into a named definition.

## Old

The original module publicly imports the following modules; those imports remain public through the new foundation:

```lean
public import Sheaf.AlgebraicGeometry.CartierPoleBoundary
public import Sheaf.AlgebraicGeometry.GeoCartierCycleClass
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Sheaf.Paper.DivisibleExtensionDerivedReduction
public import Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
```

```lean
def cartierIntegralSourceComparison {D Z : Scheme.{u}} (i : D ⟶ Z) :
    (comparisonUpperStar AddCommGrpCat.{u + 1} Z).obj
        ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj (Etale.supportedIntegralConstant D)) ⟶
      (lowerStar AddCommGrpCat.{u + 1} i).obj
        ((constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  (lowerStarComparisonUpperStarBaseChange i AddCommGrpCat.{u + 1}).app
      (Etale.supportedIntegralConstant D) ≫
    (lowerStar AddCommGrpCat.{u + 1} i).map
      (((((constantSheafAdj D.smallEtaleTopology AddCommGrpCat.{u + 1}
        (Scheme.Etale.isTerminalMkId D)).comp
          (comparisonAdjunction AddCommGrpCat.{u + 1} D)).ofNatIsoRight
        ((Scheme.toProEt D).sheafPushforwardContinuousCompSheafSectionsObjIso
          AddCommGrpCat.{u + 1} D.smallEtaleTopology (Scheme.ProEt.topology D)
          (op (Scheme.Etale.mk (𝟙 D))))).leftAdjointUniq
        (constantSheafAdj (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}
          (Scheme.ProEt.isTerminalMkId D))).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom
```

```lean
def cartierProBoundary {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (β : Ext ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
      (Etale.supportedIntegralConstant D)) Z.gmSheaf 1) :=
  (Ext.mk₀ (cartierIntegralSourceIso i).inv).comp
    ((β.mapExactFunctor (comparisonUpperStar AddCommGrpCat.{u + 1} Z)).comp
      (Ext.mk₀ (cartierUnitsComparison Z)) (add_zero 1)) (zero_add 1)
```

```lean
def cartierEtaleKummerUnit (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : (n : A) = 0) (Z : Scheme.{u}) (hZ : IsUnit (n : Γ(Z, ⊤))) :=
  (Z.kummerSequence_shortExact n hZ).extClass.comp
    (Ext.mk₀ (Etale.ordinaryFiniteRootMap A n hA Z)) (add_zero 1)
```

```lean
def cartierProKummerUnit (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : (n : A) = 0) (Z : Scheme.{u}) (hn : 0 < n)
    (hZ : IsUnit (n : Γ(Z, ⊤))) :=
  (cartierProKummer_exact Z n hn hZ).extClass.comp
    (Ext.mk₀ (cartierProRootMap A n hA Z hn hZ)) (add_zero 1)
```

```lean
def CartierEtaleReductionSpec (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : (n : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hZ : IsUnit (n : Γ(Z, ⊤)))
    (c : Ext ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
      (Etale.ordinaryFiniteConstant A D)) (Scheme.finiteEtaleTateLine Z n A hA) 2) : Prop :=
  (Ext.mk₀ (Etale.supportedIntegralGenerator A i)).comp
      (c.mapExactFunctor (Etale.RawModuleScalarComparison.forget A Z)) (zero_add 2) =
    (Etale.cartierPoleBoundary i hI).comp (cartierEtaleKummerUnit A n hA Z hZ)
      (rfl : 1 + 1 = 2)
```

```lean
def CartierProReductionSpec (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : (n : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hn : 0 < n) (hZ : IsUnit (n : Γ(Z, ⊤)))
    (c : GeoCartierClass A n hA i) : Prop :=
  (Ext.mk₀ (cartierProIntegralGenerator A i)).comp
      (c.mapExactFunctor (cartierForget A Z)) (zero_add 2) =
    (cartierProBoundary i (Etale.cartierPoleBoundary i hI)).comp
      (cartierProKummerUnit A n hA Z hn hZ) (rfl : 1 + 1 = 2)
```

```lean
def CartierScalarUnit
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B] [HasExt.{wE} B]
    (U : C ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (F : B) (H : C) (n : ℕ) (e : Ext F (U.obj H) n) : Prop :=
  ∀ K : DerivedCategory C,
    Function.Bijective (fun f : ((DerivedCategory.singleFunctor C 0).obj H)⟦(n : ℤ)⟧ ⟶ K ↦
      e.hom ≫ ((U.mapDerivedCategorySingleFunctor 0).inv.app H)⟦(n : ℤ)⟧' ≫
        (U.mapDerivedCategory.commShiftIso (n : ℤ)).inv.app
          ((DerivedCategory.singleFunctor C 0).obj H) ≫ U.mapDerivedCategory.map f)
```

## New

The original module now has `public import Sheaf.AlgebraicGeometry.CartierReductionData`. The foundation retains the public imports above and the old names. Its added public import of DerivedScalarExtUnit supplies the named, definitionally identical scalar-unit predicate.


```lean
def cartierIntegralConstantComparisonIso (D : Scheme.{u}) :
    (comparisonUpperStar AddCommGrpCat.{u + 1} D).obj
        (Etale.supportedIntegralConstant D) ≅
      (constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  (((((constantSheafAdj D.smallEtaleTopology AddCommGrpCat.{u + 1}
        (Scheme.Etale.isTerminalMkId D)).comp
          (comparisonAdjunction AddCommGrpCat.{u + 1} D)).ofNatIsoRight
        ((Scheme.toProEt D).sheafPushforwardContinuousCompSheafSectionsObjIso
          AddCommGrpCat.{u + 1} D.smallEtaleTopology (Scheme.ProEt.topology D)
          (op (Scheme.Etale.mk (𝟙 D))))).leftAdjointUniq
        (constantSheafAdj (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}
          (Scheme.ProEt.isTerminalMkId D))).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
```

```lean
def cartierBoundaryImage
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{wC} C]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{wB} B]
    (U : C ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {F G : C} {F' G' : B} (s : F' ⟶ U.obj F) (t : U.obj G ⟶ G')
    (β : Ext.{wC} F G 1) : Ext.{wB} F' G' 1 :=
  (Ext.mk₀ s).comp ((β.mapExactFunctor U).comp (Ext.mk₀ t) (add_zero 1)) (zero_add 1)
```

```lean
def cartierKummerClass
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{wC} C]
    {S : ShortComplex C} (hS : S.ShortExact) {H : C} (f : S.X₁ ⟶ H) :
    Ext.{wC} S.X₃ H 1 :=
  (ShortComplex.ShortExact.extClass.{wC} hS).comp (Ext.mk₀ f) (add_zero 1)
```

```lean
def cartierScalarBoundaryEquation
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{wC} C]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{wB} B]
    (U : C ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {F G : B} {P Q : C} (η : F ⟶ U.obj P) (c : Ext.{wC} P Q 2)
    (β : Ext.{wB} F G 1) (κ : Ext.{wB} G (U.obj Q) 1) : Prop :=
  (Ext.mk₀ η).comp (c.mapExactFunctor U) (zero_add 2) = β.comp κ (rfl : 1 + 1 = 2)
```

```lean
def cartierIntegralSourceComparison {D Z : Scheme.{u}} (i : D ⟶ Z) :
    (comparisonUpperStar AddCommGrpCat.{u + 1} Z).obj
        ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj (Etale.supportedIntegralConstant D)) ⟶
      (lowerStar AddCommGrpCat.{u + 1} i).obj
        ((constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  (lowerStarComparisonUpperStarBaseChange i AddCommGrpCat.{u + 1}).app
      (Etale.supportedIntegralConstant D) ≫
    (lowerStar AddCommGrpCat.{u + 1} i).map
      (cartierIntegralConstantComparisonIso D).hom
```

```lean
def cartierProBoundary {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (β : Ext.{u + 1} ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
      (Etale.supportedIntegralConstant D)) Z.gmSheaf 1) :
    Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj
      ((constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) (Scheme.proEtaleUnitsSheaf Z) 1 :=
  cartierBoundaryImage (comparisonUpperStar AddCommGrpCat.{u + 1} Z)
    (cartierIntegralSourceIso i).inv (cartierUnitsComparison Z) β
```

```lean
def cartierEtaleKummerUnit (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : (n : A) = 0) (Z : Scheme.{u}) (hZ : IsUnit (n : Γ(Z, ⊤))) :
    Ext.{u + 1} Z.gmSheaf ((Etale.RawModuleScalarComparison.forget A Z).obj
      (Scheme.finiteEtaleTateLine Z n A hA)) 1 :=
  cartierKummerClass (Z.kummerSequence_shortExact n hZ)
    (Etale.ordinaryFiniteRootMap A n hA Z)
```

```lean
def cartierProKummerUnit (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : (n : A) = 0) (Z : Scheme.{u}) (hn : 0 < n)
    (hZ : IsUnit (n : Γ(Z, ⊤))) :
    Ext.{u + 1} (Scheme.proEtaleUnitsSheaf Z)
      ((cartierForget A Z).obj (geoCartierLine A n hA Z)) 1 :=
  cartierKummerClass (cartierProKummer_exact Z n hn hZ)
    (cartierProRootMap A n hA Z hn hZ)
```

```lean
def CartierEtaleReductionSpec (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : (n : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hZ : IsUnit (n : Γ(Z, ⊤)))
    (c : Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
      (Etale.ordinaryFiniteConstant A D)) (Scheme.finiteEtaleTateLine Z n A hA) 2) : Prop :=
  cartierScalarBoundaryEquation (Etale.RawModuleScalarComparison.forget A Z)
    (Etale.supportedIntegralGenerator A i) c (Etale.cartierPoleBoundary i hI)
    (cartierEtaleKummerUnit A n hA Z hZ)
```

```lean
def CartierProReductionSpec (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : (n : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hn : 0 < n) (hZ : IsUnit (n : Γ(Z, ⊤)))
    (c : GeoCartierClass A n hA i) : Prop :=
  cartierScalarBoundaryEquation (cartierForget A Z) (cartierProIntegralGenerator A i) c
    (cartierProBoundary i (Etale.cartierPoleBoundary i hI))
    (cartierProKummerUnit A n hA Z hn hZ)
```

```lean
def CartierScalarUnit
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B] [HasExt.{wE} B]
    (U : C ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (F : B) (H : C) (n : ℕ) (e : Ext F (U.obj H) n) : Prop :=
  U.DerivedExtUnit F H n e
```

## Users

The downstream declaration-use queries are recorded in scratchpad/consumer-uses.txt. Their complete
set of existing modules that mention any changed definition is the two rows below. All 33 transitive
module importers retain the same exported names; the only direct importer is the boundary helper.
The generic predicate and new helper-module consumers are included in this packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | N1 | Same public statement; all three proofs completed using the foundation. |
| Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence | unclaimed | Proof import changes to the foundation; explicit unfolding of two definitionally identical aliases preserves the proof and signature. |
| Sheaf.AlgebraicGeometry.CartierReductionData | N1, new | Preserves the constructions and declares the proved existence theorems; named aliases contain actual data or propositions. |
| Sheaf.AlgebraicGeometry.CartierEtaleKummerDerivedUnit | N1, new | Uses the unchanged etale Kummer class and scalar-unit predicate. |
| Sheaf.AlgebraicGeometry.CartierProKummerDerivedUnit | N1, new | Uses the unchanged pro-etale Kummer class and scalar-unit predicate. |
| Sheaf.AlgebraicGeometry.CartierProIntegralDerivedUnit | N1, new | Uses the unchanged supported integral generator and scalar-unit predicate. |
| Sheaf.AlgebraicGeometry.CartierProIntegralResidueDerivedUnit | N1, new | Transports the exact quotient sequence through the canonical comparisons. |
| Sheaf.AlgebraicGeometry.CartierProRootScalar | N1, new | Proves the pure-tensor normalization for the existing root map. |
| Sheaf.AlgebraicGeometry.CartierProIntegralScalar | N1, new | Proves the constant-generator normalization for the existing source map. |
| Sheaf.AlgebraicGeometry.ComparisonConstantGenerator | N1, new | Proves the normalization of the canonical constant comparison. |

The unchanged OrdinarySupportedCartierKummer source was compiled against the adapted boundary helper.
No adaptation of that source is delivered. The current SupportedKummerScalarSource and ordinary scalar predicate are retained verbatim;
the separate scalar record documents the proof-level rebase. No existing mathematical assertion is weakened,
strengthened, or replaced. All chosen Cartier data still come from uniqueness theorems determining
their actual Ext class. There is no arbitrary witness selection in a definition.

The definitions appear below the targets, so the definition review for each target that uses them
is reopened for the independent reader. Their meanings are unchanged: every body replacement above
unfolds to the old expression, and the full unbounded Hom quantifier is retained.

## Status

landed 20261021T012410-L-2185565 2026-10-21 (merge of deliver/N1/Sheaf.AlgebraicGeometry.CartierReductionSiteComparison)
