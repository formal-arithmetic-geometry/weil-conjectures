# AlgebraicGeometry.Scheme.purIntegralReduction and companion chart constructions

## Reason

The finite simultaneous-chart lemma is a genuine separate part of the source argument.
It supplies the integral representatives and quotient models; the item's proof derives
all-module Tor amplitude, intrinsic constructibility, and boundedness of retained etale
origins. Its statement needs the five existing constructions, so they must precede both
lemmas without a circular import. Move them verbatim into the new chart module and
publicly import that module from the original one. No construction, type, name, universe,
visibility, or target statement changes. No data are selected by a new definition.

## Old

The following declarations were in Sheaf.Paper.PurIntegralReductionUniformTor:

```lean
/-- The actual completed-ring reduction in the equivalent fixed-module presentation.
Index n denotes the positive exponent n+1. Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purIntegralReduction (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (K : PbcCompletedDerived T d) (n : ℕ) :=
  (pbcDerivedFunctionRealization T d n).asEquivalence.inverse.obj
    ((pbcCompletedReduction T d n).obj K)

/-- Termwise reduction of a scalar complex along the specified quotient map.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purScalarReductionComplex {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (n : ℕ) :=
  letI := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).left_adjoint_additive
  ((ModuleCat.extendScalars (Ideal.Quotient.mk (d.ideal ^ (n + 1))) :
    ModuleCat.{u + 1} A ⥤ ModuleCat.{u + 1} (PbcQuotient d n)).mapHomologicalComplex
      (.up ℤ)).obj P

/-- Exact restriction of a reduction to an immersed stratum.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purReductionOnStratum {T Z : Scheme.{u}} (g : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) (n : ℕ) :=
  ((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} (PbcQuotient d n)) g)
    |>.mapDerivedCategory).obj (purIntegralReduction T d K n)

/-- Exact slice restriction of a derived finite-coefficient complex.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purFixedChart (Z : Scheme.{u}) (B : Type (u + 1)) [CommRing B] (U : Z.ProEt)
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} B))) :
    _root_.DerivedCategory (Sheaf ((ProEt.topology Z).over U) (ModuleCat.{u + 1} B)) :=
  (@CategoryTheory.derivedSliceRestriction.{u} Z.ProEt _
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology Z) B _ U).obj K

/-- A scalar quotient complex realized on the actual localized pro-etale site.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purScalarComplexOnChart (Z : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (U : Z.ProEt)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (n : ℕ) :=
  (DerivedCategory.Q (C := Sheaf ((ProEt.topology Z).over U)
    (ModuleCat.{u + 1} (PbcQuotient d n)))).obj
      (((constantSheaf ((ProEt.topology Z).over U)
        (ModuleCat.{u + 1} (PbcQuotient d n))).mapHomologicalComplex (.up ℤ)).obj
          (purScalarReductionComplex d P n))
```

## New

The same declarations, with exactly the same bodies and public visibility, are in
Sheaf.Paper.PurIntegralFinitePerfectCharts. The original module publicly imports that
module. Existing importers see exactly the same declarations.

```lean
public import Sheaf.Paper.PurIntegralFinitePerfectCharts

/-- The actual completed-ring reduction in the equivalent fixed-module presentation.
Index n denotes the positive exponent n+1. Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purIntegralReduction (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (K : PbcCompletedDerived T d) (n : ℕ) :=
  (pbcDerivedFunctionRealization T d n).asEquivalence.inverse.obj
    ((pbcCompletedReduction T d n).obj K)

/-- Termwise reduction of a scalar complex along the specified quotient map.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purScalarReductionComplex {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (n : ℕ) :=
  letI := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).left_adjoint_additive
  ((ModuleCat.extendScalars (Ideal.Quotient.mk (d.ideal ^ (n + 1))) :
    ModuleCat.{u + 1} A ⥤ ModuleCat.{u + 1} (PbcQuotient d n)).mapHomologicalComplex
      (.up ℤ)).obj P

/-- Exact restriction of a reduction to an immersed stratum.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purReductionOnStratum {T Z : Scheme.{u}} (g : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) (n : ℕ) :=
  ((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} (PbcQuotient d n)) g)
    |>.mapDerivedCategory).obj (purIntegralReduction T d K n)

/-- Exact slice restriction of a derived finite-coefficient complex.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purFixedChart (Z : Scheme.{u}) (B : Type (u + 1)) [CommRing B] (U : Z.ProEt)
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} B))) :
    _root_.DerivedCategory (Sheaf ((ProEt.topology Z).over U) (ModuleCat.{u + 1} B)) :=
  (@CategoryTheory.derivedSliceRestriction.{u} Z.ProEt _
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology Z) B _ U).obj K

/-- A scalar quotient complex realized on the actual localized pro-etale site.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purScalarComplexOnChart (Z : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (U : Z.ProEt)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (n : ℕ) :=
  (DerivedCategory.Q (C := Sheaf ((ProEt.topology Z).over U)
    (ModuleCat.{u + 1} (PbcQuotient d n)))).obj
      (((constantSheaf ((ProEt.topology Z).over U)
        (ModuleCat.{u + 1} (PbcQuotient d n))).mapHomologicalComplex (.up ℤ)).obj
          (purScalarReductionComplex d P n))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PurIntegralReductionUniformTor | T9 | Same theorem signature; proof now uses charts and Tor descent. |
| Sheaf.Paper.PurIntegralFinitePerfectCharts | T9 (new in this delivery) | Owns the five unchanged constructions and states the chart-selection lemma. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed | Same reexported interface; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Same reexported interface; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Same reexported interface; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Same reexported interface; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Same reexported interface; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Same reexported interface; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | K9 | Same reexported interface; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | unclaimed | Same reexported interface; no adaptation. |

The current read-only downstream query found the eight consumers listed above (seven
direct, one transitive), and only the item itself using purIntegralReduction. None
mentions any of the five relocated abbreviations. Every original public import is
preserved, and the new public import reexports the identical constructions. The DAG attachment and dependency route are retained; this is no withdrawal.
None of the other original public imports is removed. No consumer adaptation is needed.
The maintainer's independent reader checks the relocated declarations and reexport.

## Status

landed 20261025T024000-L-2494315 2026-10-25 (merge of deliver/T9/Sheaf.Paper.PurIntegralReductionUniformTor)
