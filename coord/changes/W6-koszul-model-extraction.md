# reconstructionKoszulDerivedUnit and Koszul reconstruction model extraction

## Reason

The returned comparison must be proved from the strict augmentation and normalized
Roos comparison without a cyclic import. Extracting the existing models separates
these definitions from the theorem that uses the comparison. Public imports and
instance attributes must remain available to every original consumer.

## Old

All support declarations preceded `koszulReconstruction` in
`Sheaf.Paper.KoszulReconstruction`. Its public import block was:

```lean
public import Sheaf.Paper.CompletedAdicCoefficientDatum
public import Sheaf.Paper.CompletedAdicIntrinsicCompletion
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Localization.Predicate
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
```

The localization unit definition was:

```lean
def reconstructionKoszulDerivedUnit (r : ℕ) (a : Fin r → A) :
    𝟭 (DerivedCategory (CompletedAdicModules T d)) ⟶
      reconstructionKoszulDerivedFunctor T d r a :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (CompletedAdicModules T d) (ComplexShape.up ℤ))
      DerivedCategory.Q (𝟭 (DerivedCategory (CompletedAdicModules T d))) :=
    ⟨Functor.rightUnitor _⟩
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (CompletedAdicModules T d) (ComplexShape.up ℤ))
    DerivedCategory.Q (reconstructionKoszulFiberFunctor T d r a ⋙ DerivedCategory.Q)
    (𝟭 _) (reconstructionKoszulDerivedFunctor T d r a)
    (Functor.whiskerRight (reconstructionKoszulComplexUnit T d r a) DerivedCategory.Q)
```

## New

`Sheaf.Paper.KoszulReconstruction` publicly imports
`Sheaf.Paper.KoszulReconstructionModels` and privately imports the proved comparison.
The models module retains the original public import block verbatim. Every original
public support declaration, instance attribute, signature and namespace is retained.
Private generic helpers remain private; the comparison accesses them with `import all`.
There is no target statement change and no mathematical data replacement.

The unit now specifies explicitly the canonical localization lifting instance that
was previously synthesized:

```lean
def reconstructionKoszulDerivedUnit (r : ℕ) (a : Fin r → A) :
    𝟭 (DerivedCategory (CompletedAdicModules T d)) ⟶
      reconstructionKoszulDerivedFunctor T d r a :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (CompletedAdicModules T d) (ComplexShape.up ℤ))
      DerivedCategory.Q (𝟭 (DerivedCategory (CompletedAdicModules T d))) :=
    ⟨Functor.rightUnitor _⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (CompletedAdicModules T d) (ComplexShape.up ℤ))
      (reconstructionKoszulFiberFunctor T d r a ⋙ DerivedCategory.Q)
      (reconstructionKoszulDerivedFunctor T d r a) :=
    Localization.liftingLift _ (reconstructionKoszulFiberFunctor_inverts T d r a) _
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (CompletedAdicModules T d) (ComplexShape.up ℤ))
    DerivedCategory.Q (reconstructionKoszulFiberFunctor T d r a ⋙ DerivedCategory.Q)
    (𝟭 _) (reconstructionKoszulDerivedFunctor T d r a)
    (Functor.whiskerRight (reconstructionKoszulComplexUnit T d r a) DerivedCategory.Q)
```

The explicit instance is `Localization.liftingLift`; its comparison is the same
`Localization.fac` used by the existing model. Thus the unit remains the localization
of exactly the original degree-zero chain unit. This makes the comparison formula
usable without costly instance unfolding.

The proof of `reconstructionKoszulProductMap_comm` now uses the naturality theorem
for `towerTransitionEndomorphism` and a proved private tensor-square lemma, rather
than unfolding the product and total-complex construction. No non-proof part of
that declaration changes. The only additional private proof import is
`WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism`.

The generic localization assembly, exact-products Roos comparison and completed
Koszul augmentation are new modules under `Sheaf`. All data constructions are explicit;
the only retained hole is the strictly smaller augmentation theorem, as permitted
by the return. No source-library module is edited.

## Users

The consumer search includes the live direct importer and the preserved quarantined
sources. None is adapted or withdrawn by this packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedAdicLevelwiseIsomorphismCones | unclaimed | live; public model names and instances remain available |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed | quarantined; tested unchanged against the extraction |
| Sheaf.Paper.CompletedCompactSupportExchange | unclaimed | quarantined; tested unchanged against the extraction |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | quarantined; tested unchanged against the extraction |
| Sheaf.Paper.FinitePerfectAdicRealization | B3 | quarantined; tested unchanged against the extraction |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | unclaimed | quarantined; tested unchanged against the extraction |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | unclaimed | quarantined; tested unchanged against the extraction |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | unclaimed | quarantined; tested unchanged against the extraction |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | quarantined; tested unchanged against the extraction |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | unclaimed | quarantined; tested unchanged against the extraction |
| Sheaf.Paper.ReconstructionUniformTower | B7 | quarantined; tested unchanged against the extraction |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | quarantined; tested unchanged against the extraction |
| Sheaf.Paper.IntegralPullbackCompletedComparison | unclaimed | quarantined; tested unchanged against the extraction |
| Sheaf.Paper.IntegralCanonicalTruncations | unclaimed | quarantined; tested unchanged against the extraction |
| Sheaf.Paper.CompletedReductionSquare | unclaimed | quarantined; tested unchanged against the extraction |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | quarantined; tested unchanged against the extraction |
| Sheaf.Paper.KoszulReconstruction | W6 | Same target statement, now proved through the comparison. |
| Sheaf.Paper.KoszulReconstructionComparison | W6 packet | Proved localization descent and unit normalization. |
| Sheaf.Paper.CompletedKoszulQuotientRoosAugmentation | W6 packet | Uses unchanged model constructions. |

Baseline consumer checks pass for 13 modules. The quarantined
`FinitePerfectAdicRealization` and `ReconstructionUniformTower` already fail because
of missing declarations; `OrderedExchangeCoefficientComparison` already exceeds
the per-file limit. Against the extracted models, 14 of the 16 unchanged consumers pass, including
`OrderedExchangeCoefficientComparison`. The same two quarantined consumers fail
with their pre-existing missing declarations (and the existing line-560 heartbeat
limit in `ReconstructionUniformTower`). No regression or forced adaptation was found.
The full before/after table is in report.md.

## Status

landed 20261020T230846-L-622028 2026-10-20 (merge of deliver/W6/Sheaf.Paper.KoszulReconstruction)
