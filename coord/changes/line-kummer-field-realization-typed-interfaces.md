# Line Kummer field realization timeout repair

## Reason

Restore the item archived for the 60-second compile failure in coord/rework.tsv.
The degree-zero Tate representatives previously used reducible abbreviations with
inferred result types. They now have explicit derived-category types and ordinary
semireducible definitions, with exactly the original bodies. The eight generic,
class, comparison and compact-map definitions are irreducible, so consumers use
their interfaces rather than expand the construction. The two class definitions
use the same Ext realization and unique Cartier-family projections, avoiding the
unnecessary unfolding of the supported constant target before applying extPlusMap.
No construction, hypothesis, normalization or target statement changes.

The original main theorem and all existing declarations are retained. The only
remaining sorry is the original theorem. There are no new declarations or nodes.
The complete repaired file compiled in 42.7 seconds through lcompile.py.

## Old

Archived source: quarantine/Sheaf/Paper/LineKummerFieldRealization.lean.

```lean
def singleShiftInclusion {C : Type v} [Category.{w} C] [Abelian C]
    [HasDerivedCategory C] (M : C) :
    DerivedCategory.Plus.ι.obj
      (((DerivedCategory.Plus.singleFunctor C 0).obj M)⟦(2 : ℤ)⟧) ≅
        ((DerivedCategory.singleFunctor C 0).obj M)⟦(2 : ℤ)⟧ :=
  (DerivedCategory.Plus.ι.commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso ((DerivedCategory.Plus.singleFunctorιIso C 0).app M)

def extPlusMap {C : Type v} [Category.{w} C] [Abelian C] [HasDerivedCategory C]
    [HasExt.{w} C] {M N : C} (κ : Ext M N 2) :
    (DerivedCategory.Plus.singleFunctor C 0).obj M ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj N)⟦(2 : ℤ)⟧ :=
  DerivedCategory.Plus.ι.preimage
    ((DerivedCategory.Plus.singleFunctorιIso C 0).hom.app M ≫ κ.hom ≫
      (singleShiftInclusion N).inv)

variable (l : ℕ) [Fact l.Prime] (F : Type u) [Field F]
  [Algebra (Padic l) F] [FiniteDimensional (Padic l) F] (n : ℕ)

abbrev etaleLine (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    (T : Scheme.{u}) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj
    (finiteEtaleTateLine T (l ^ (n + 1)) (finiteTateCoefficient l F n) hA)

abbrev proLine (T : Scheme.{u}) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj (finiteTateProSheaf l F n T 1)

def etaleClass
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))) :
    SectionCompactSource.etaleSupported (finiteTateCoefficient l F n) i ⟶
      (etaleLine l F n hA T)⟦(2 : ℤ)⟧ :=
  by
    unfold SectionCompactSource.etaleSupported SupportedConstantNormalization.supported
      SupportedConstantNormalization.push SupportedConstantNormalization.constant
    exact extPlusMap
      ((Etale.cartier_kummer_map l F).2.exists.choose.1 n n hA i hI hT)

def proClass {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))) :
    SectionCompactSource.proSupported (finiteTateCoefficient l F n) i ⟶
      (proLine l F n T)⟦(2 : ℤ)⟧ :=
  by
    unfold SectionCompactSource.proSupported SupportedConstantNormalization.supported
      SupportedConstantNormalization.push SupportedConstantNormalization.constant
    let κ := (Etale.cartier_kummer_map l F).2.exists.choose.2 n i hI hT
    unfold Etale.cartierSupported at κ
    exact extPlusMap κ

def shiftedComparison
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    (T : Scheme.{u})
    (q : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T).obj
        (finiteEtaleTateLine T (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
          finiteTateProSheaf l F n T 1) :
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T).mapDerivedCategoryPlus.obj
        ((etaleLine l F n hA T)⟦(2 : ℤ)⟧) ≅ (proLine l F n T)⟦(2 : ℤ)⟧ :=
  ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T).mapDerivedCategoryPlus.commShiftIso
        (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      ((Functor.mapDerivedCategoryPlusSingleFunctor
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T) 0).app _ ≪≫
        (DerivedCategory.Plus.singleFunctor _ 0).mapIso q)

def etaleTau
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    {B X : Scheme.{u}} {π : X ⟶ B} (c : Compactification π)
    (z : B ⟶ X) [IsClosedImmersion z] (hz : z ≫ π = 𝟙 B)
    (hI : z.ker.IsInvertible) (hX : IsUnit (l : Γ(X, ⊤))) :=
  (SectionCompactSource.etaleSource (finiteTateCoefficient l F n) c z hz).hom ≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).map
        (etaleClass l F n hA z hI hX)

def proTau {B X : Scheme.{u}} {π : X ⟶ B} (c : Compactification π)
    (z : B ⟶ X) [IsClosedImmersion z] (hz : z ≫ π = 𝟙 B)
    (hI : z.ker.IsInvertible) (hX : IsUnit (l : Γ(X, ⊤))) :=
  SectionCompactSource.proSource (finiteTateCoefficient l F n) c z hz ≫
    (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).map
        (proClass l F n z hI hX)

def compactTarget
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    {B X : Scheme.{u}} {π : X ⟶ B} (c : Compactification π)
    (q : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) X).obj
        (finiteEtaleTateLine X (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
          finiteTateProSheaf l F n X 1) :=
  (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).mapIso
        (shiftedComparison l F n hA X q).symm ≪≫
    (ProEtale.compactSupportSiteComparisonPlus (finiteTateCoefficient l F n) c).symm.app
      ((etaleLine l F n hA X)⟦(2 : ℤ)⟧)
```

## New

The following definitions singleShiftInclusion, extPlusMap, etaleClass, proClass,
shiftedComparison, etaleTau, proTau and compactTarget carry @[irreducible].

```lean
def singleShiftInclusion {C : Type v} [Category.{w} C] [Abelian C]
    [HasDerivedCategory C] (M : C) :
    DerivedCategory.Plus.ι.obj
      (((DerivedCategory.Plus.singleFunctor C 0).obj M)⟦(2 : ℤ)⟧) ≅
        ((DerivedCategory.singleFunctor C 0).obj M)⟦(2 : ℤ)⟧ :=
  (DerivedCategory.Plus.ι.commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso ((DerivedCategory.Plus.singleFunctorιIso C 0).app M)

def extPlusMap {C : Type v} [Category.{w} C] [Abelian C] [HasDerivedCategory C]
    [HasExt.{w} C] {M N : C} (κ : Ext M N 2) :
    (DerivedCategory.Plus.singleFunctor C 0).obj M ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj N)⟦(2 : ℤ)⟧ :=
  DerivedCategory.Plus.ι.preimage
    ((DerivedCategory.Plus.singleFunctorιIso C 0).hom.app M ≫ κ.hom ≫
      (singleShiftInclusion N).inv)

variable (l : ℕ) [Fact l.Prime] (F : Type u) [Field F]
  [Algebra (Padic l) F] [FiniteDimensional (Padic l) F] (n : ℕ)

def etaleLine (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    (T : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n))) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj
    (finiteEtaleTateLine T (l ^ (n + 1)) (finiteTateCoefficient l F n) hA)

def proLine (T : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n))) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj (finiteTateProSheaf l F n T 1)

def etaleClass
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))) :
    SectionCompactSource.etaleSupported (finiteTateCoefficient l F n) i ⟶
      (etaleLine l F n hA T)⟦(2 : ℤ)⟧ :=
  by
    exact extPlusMap
      ((Etale.cartier_kummer_map l F).2.exists.choose.1 n n hA i hI hT)

def proClass {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))) :
    SectionCompactSource.proSupported (finiteTateCoefficient l F n) i ⟶
      (proLine l F n T)⟦(2 : ℤ)⟧ :=
  by
    let κ := (Etale.cartier_kummer_map l F).2.exists.choose.2 n i hI hT
    unfold Etale.cartierSupported at κ
    exact extPlusMap κ

def shiftedComparison
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    (T : Scheme.{u})
    (q : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T).obj
        (finiteEtaleTateLine T (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
          finiteTateProSheaf l F n T 1) :
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T).mapDerivedCategoryPlus.obj
        ((etaleLine l F n hA T)⟦(2 : ℤ)⟧) ≅ (proLine l F n T)⟦(2 : ℤ)⟧ :=
  ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T).mapDerivedCategoryPlus.commShiftIso
        (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      ((Functor.mapDerivedCategoryPlusSingleFunctor
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T) 0).app _ ≪≫
        (DerivedCategory.Plus.singleFunctor _ 0).mapIso q)

def etaleTau
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    {B X : Scheme.{u}} {π : X ⟶ B} (c : Compactification π)
    (z : B ⟶ X) [IsClosedImmersion z] (hz : z ≫ π = 𝟙 B)
    (hI : z.ker.IsInvertible) (hX : IsUnit (l : Γ(X, ⊤))) :=
  (SectionCompactSource.etaleSource (finiteTateCoefficient l F n) c z hz).hom ≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).map
        (etaleClass l F n hA z hI hX)

def proTau {B X : Scheme.{u}} {π : X ⟶ B} (c : Compactification π)
    (z : B ⟶ X) [IsClosedImmersion z] (hz : z ≫ π = 𝟙 B)
    (hI : z.ker.IsInvertible) (hX : IsUnit (l : Γ(X, ⊤))) :=
  SectionCompactSource.proSource (finiteTateCoefficient l F n) c z hz ≫
    (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).map
        (proClass l F n z hI hX)

def compactTarget
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    {B X : Scheme.{u}} {π : X ⟶ B} (c : Compactification π)
    (q : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) X).obj
        (finiteEtaleTateLine X (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
          finiteTateProSheaf l F n X 1) :=
  (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).mapIso
        (shiftedComparison l F n hA X q).symm ≪≫
    (ProEtale.compactSupportSiteComparisonPlus (finiteTateCoefficient l F n) c).symm.app
      ((etaleLine l F n hA X)⟦(2 : ℤ)⟧)
```

## Users

| module | current holder | adaptation |
| --- | --- | --- |
| Sheaf.Paper.LineKummerFieldRealization | M3 | Own assigned timeout repair. |

Searches across lean/ and quarantine/ found no Lean importer or qualified consumer.
The absent source makes tools/downstream.py report unknown module, so direct source
and DAG parent searches were used. The DAG parent lem-pur-line-zero-class-exchange
still needs this item: its attachment, all dependencies, and the unit route remain.
No other module or source-library declaration changes. All original public imports
stay, and the six unused private proof-plan imports are removed.

## Status

landed 20261024T015216-L-2340150 2026-10-24 (merge of deliver/M3/Sheaf.Paper.LineKummerFieldRealization)
