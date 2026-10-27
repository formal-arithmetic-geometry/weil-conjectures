# Line Kummer compact-image type boundaries

## Reason

The assigned rework row records a 60-second timeout for this module. While this
session was reading its archived source, the shared tree acquired M3's landed
repair (line-kummer-field-realization-typed-interfaces.md). This delivery starts
from that repaired source and preserves all of it.

The remaining compact-image definitions inferred their result types by expanding
compositions, functor maps and natural isomorphisms. Give etaleTau, proTau and
compactTarget explicit source and target types, so later definitions elaborate
against those interfaces. Make intrinsicLine an ordinary semireducible definition,
matching the already repaired etaleLine and proLine, to avoid automatic expansion
of the prescribed intrinsic Tate complex in cohomology and Tor predicates.
All four bodies are unchanged. All objects, arrows, normalizations and mathematical
statements are unchanged, including the main theorem. This is a definition repair;
it closes no proof hole and introduces none. The entire changed module compiled
through lcompile.py in 41.5 seconds with no errors or warnings.

## Old

```lean
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

abbrev intrinsicLine (T : Scheme.{u}) :
    proEtaleDerivedCategory T (Padic.coefficientExtensionRing l F (n + 1)) :=
  (DerivedCategory.singleFunctor _ 0).obj (WeilConjectures.finiteCoefficientTwist l F T n 1)
```

## New

```lean
def etaleTau
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    {B X : Scheme.{u}} {π : X ⟶ B} (c : Compactification π)
    (z : B ⟶ X) [IsClosedImmersion z] (hz : z ≫ π = 𝟙 B)
    (hI : z.ker.IsInvertible) (hX : IsUnit (l : Γ(X, ⊤))) :
    SectionCompactSource.etaleConstant (finiteTateCoefficient l F n) B ⟶
      (Etale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).obj
          ((etaleLine l F n hA X)⟦(2 : ℤ)⟧) :=
  (SectionCompactSource.etaleSource (finiteTateCoefficient l F n) c z hz).hom ≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).map
        (etaleClass l F n hA z hI hX)

def proTau {B X : Scheme.{u}} {π : X ⟶ B} (c : Compactification π)
    (z : B ⟶ X) [IsClosedImmersion z] (hz : z ≫ π = 𝟙 B)
    (hI : z.ker.IsInvertible) (hX : IsUnit (l : Γ(X, ⊤))) :
    SectionCompactSource.proConstant (finiteTateCoefficient l F n) B ⟶
      (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).obj
          ((proLine l F n X)⟦(2 : ℤ)⟧) :=
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
          finiteTateProSheaf l F n X 1) :
    (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).obj
        ((proLine l F n X)⟦(2 : ℤ)⟧) ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) B).mapDerivedCategoryPlus.obj
          ((Etale.rightDerivedLowerShriekOfCompactificationPlus
            (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).obj
              ((etaleLine l F n hA X)⟦(2 : ℤ)⟧)) :=
  (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).mapIso
        (shiftedComparison l F n hA X q).symm ≪≫
    (ProEtale.compactSupportSiteComparisonPlus (finiteTateCoefficient l F n) c).symm.app
      ((etaleLine l F n hA X)⟦(2 : ℤ)⟧)

def intrinsicLine (T : Scheme.{u}) :
    proEtaleDerivedCategory T (Padic.coefficientExtensionRing l F (n + 1)) :=
  (DerivedCategory.singleFunctor _ 0).obj (WeilConjectures.finiteCoefficientTwist l F T n 1)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LineKummerFieldRealization | J9 | Own definition repair; all consumers compile in this file. |

tools/downstream.py for this module and each of the four changed names reports
zero downstream modules and only occurrences in the item itself. The DAG parent
lem-pur-line-zero-class-exchange still needs the item. Its Lean attachment,
dependencies and unit route remain. No target definition changes meaning: this
only adds type annotations and changes reducibility of an identical body.

## Status

landed 20261024T190158-L-3978354 2026-10-24 (merge of deliver/J9/Sheaf.Paper.LineKummerFieldRealization)
