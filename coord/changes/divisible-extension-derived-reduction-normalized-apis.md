# SheafOfModules.DivisibleReduction.Presentation and Identifications

## Reason

Prove the five holes and keep the full module below its compile limit. Profiling
showed expensive kernel checking at specialized sheaf record types. The records
are now specializations of general structures with exactly the previous fields.
Explicit chosen-adjunction types and private normalization APIs avoid unfolding
large constructions. This changes representation, not mathematical data.

## Old

```lean
noncomputable def sheafScalarOrdinaryAdjunction :=
  Classical.choose (sheafDerivedScalarAdjunction_exists q D)

noncomputable def sheafScalarDerivedAdjunction :=
  Classical.choose (Classical.choose_spec (sheafDerivedScalarAdjunction_exists q D)).2

structure Presentation where
  S : ShortComplex (Integral J)
  exact : S.ShortExact
  H : Residue J n
  Q : Residue J n
  i : (restriction J n).obj H ⟶ S.X₁
  p : S.X₃ ⟶ (restriction J n).obj Q
  wi : i ≫ (n • 𝟙 S.X₁) = 0
  wp : (n • 𝟙 S.X₃) ≫ p = 0
  kummer : (ShortComplex.mk i (n • 𝟙 S.X₁) wi).ShortExact
  quotient : (ShortComplex.mk (n • 𝟙 S.X₃) p wp).ShortExact

structure Identifications (P : Presentation (J := J) n) where
  alphaF : D.T.obj ((DerivedCategory.singleFunctor (Integral J) 0).obj P.S.X₃) ≅
    (DerivedCategory.singleFunctor (Residue J n) 0).obj P.Q
  alphaB : D.T.obj ((DerivedCategory.singleFunctor (Integral J) 0).obj P.S.X₁) ≅
    ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H)⟦(1 : ℤ)⟧
  quotient_unit : eta n D P.S.X₃ ≫ (derivedRestriction n).map alphaF.hom ≫
    ((restriction J n).mapDerivedCategorySingleFunctor 0).hom.app P.Q =
      (DerivedCategory.singleFunctor (Integral J) 0).map P.p
  kummer_unit : eta n D P.S.X₁ ≫ (derivedRestriction n).map alphaB.hom = kappa n P
```

## New

```lean
noncomputable def sheafScalarOrdinaryAdjunction : D.E ⊣ restrictScalars.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q) :=
  Classical.choose (sheafDerivedScalarAdjunction_exists q D)

noncomputable def sheafScalarDerivedAdjunction : D.T ⊣ (restrictScalars.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q)).mapDerivedCategory :=
  Classical.choose (Classical.choose_spec (sheafDerivedScalarAdjunction_exists q D)).2

abbrev Presentation := CategoryTheory.ScalarReductionPresentation (restriction J n) n

abbrev Identifications (P : Presentation (J := J) n) :=
  CategoryTheory.NormalizedReductionIdentifications D.T (derivedRestriction n)
    ((DerivedCategory.singleFunctor (Integral J) 0).obj P.S.X₁)
    ((DerivedCategory.singleFunctor (Integral J) 0).obj P.S.X₃)
    ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H)
    ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.Q)
    ((DerivedCategory.singleFunctor (Integral J) 0).obj ((restriction J n).obj P.Q))
    (((restriction J n).mapDerivedCategorySingleFunctor 0).hom.app P.Q)
    (eta n D P.S.X₁) (eta n D P.S.X₃)
    ((DerivedCategory.singleFunctor (Integral J) 0).map P.p) (kappa n P)
```

The general structures are CategoryTheory.ScalarReductionPresentation and
CategoryTheory.NormalizedReductionIdentifications, defined in the item module
and attached to their two new definition nodes. They have exactly the old ten
and four fields, respectively. Generated projections and constructors now come
from those general structures. Existing consumers use field notation, not the
old specialized constructor or recursor names. The two adjunction definition
bodies are unchanged; their annotations equal their previously inferred types.
All public theorem signatures and the Cartier unit route stay unchanged.

The other additions are private proved APIs and two proved general theorem
modules, CokernelAdjointExchange and NormalizedScalarBoundaryNaturality. Local
irreducibility of the chosen adjunctions, coefficient unit and identifications
only controls unfolding within this file. No adopted source module changes.

## Users

The current downstream scan found 148 transitive importers. Declaration-use
scans of Presentation, Identifications and both
chosen adjunctions give the rows below, including textual false positives. All
six current direct importers are listed, together with the previously checked
CartierReductionSiteComparison. The external declaration users are
GeoCartierExponentIndependence, ResidueKummerDerivedUnit and
ResidueQuotientDerivedUnit. No consumer needs adaptation. Target meanings that
use these records must receive the standard independent definition review.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DivisibleExtensionDerivedReduction | V2 | Own item; five complete proofs and equivalent record representations. |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | unclaimed | Now a transitive importer through CartierReductionData; no signature or mathematical meaning changes. |
| Sheaf.AlgebraicGeometry.CartierReductionData | unclaimed | Current direct importer; no uses of the changed declarations and no adaptation. |
| Sheaf.AlgebraicGeometry.ResidueKummerDerivedUnit | unclaimed | Builds Presentation by its unchanged ten fields, then uses alphaB, kummer_unit and the derived adjunction Hom equivalence. The record abbreviation preserves all these types and the positive connecting class; no adaptation. |
| Sheaf.AlgebraicGeometry.ResidueQuotientDerivedUnit | unclaimed | Builds Presentation by its unchanged ten fields, then uses alphaF, quotient_unit and the derived adjunction Hom equivalence. The record abbreviation preserves the quotient normalization and the universal property against every derived object; no adaptation. |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClass | T3 | Direct importer; no signature or mathematical meaning changes. |
| Sheaf.Paper.GeoCartierExponentIndependence | unclaimed | Uses Presentation and the derived adjunction; same fields and normalized type. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | Direct importer; no signature or mathematical meaning changes. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Textual false positive: another Presentation namespace or import path; unaffected. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Textual false positive: another Presentation namespace or import path; unaffected. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Textual false positive: another Presentation namespace or import path; unaffected. |
| WeilConjectures | unclaimed | Textual false positive: another Presentation namespace or import path; unaffected. |

The previously checked external declaration user GeoCartierExponentIndependence
and direct importer GeoCartierCycleClass compiled unchanged with these definitions.
The returned packet omitted ResidueKummerDerivedUnit and
ResidueQuotientDerivedUnit from this table; both are now explicitly recorded.
Their anonymous record constructors and field projections use the same ten
presentation fields and four identification fields; neither uses a removed
specialized recursor or constructor name. Both compile unchanged against the
repaired packet: ResidueQuotientDerivedUnit in 34.3 seconds and
ResidueKummerDerivedUnit in 8.9 seconds. The item compiles in 40.6 seconds
and the two proved helper modules in 7.5 and 8.8 seconds, without warnings.
CartierReductionSiteComparison hits its 60-second limit both against the
sandbox and against the original published build; it only imports the item,
without mentioning the changed declarations. No adaptation of it is forced
by this delivery. DiagonalTowerSystem also only imports the item and times out
both with the sandbox and against the original published build. It is unchanged.

## Status

landed 20261021T061727-L-1821358 2026-10-21 (merge of deliver/V2/Sheaf.Paper.DivisibleExtensionDerivedReduction)
