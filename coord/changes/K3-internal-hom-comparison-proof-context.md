# WeilConjectures.SfbHomFilteredColimit.comparison_existsUnique

## Reason

Stage-3 preflight requests a change record for the added `open` and local `attribute`
commands in `Sheaf.Paper.DerivedInternalHomFilteredColimitData`. These commands support the private sheaf-tensor evaluation proof
and prevent expensive unfolding of the monoidal localization construction. This is
not a mathematical interface change: every existing public declaration signature,
definition body and public import is preserved. Only the theorem proof, private proved
helpers, one private proof import and the local proof elaboration context are added.

The `open` command and options affect this file's elaboration. Every added attribute
is explicitly local. The complete proof context is scoped by
`section ComparisonProof`, ending before the original `comparison` definition.
No global instance, simp rule, notation or declaration attribute
is installed for consumers. No adopted source-library file is modified.

## Old

Original declaration signature, verbatim:

```lean
theorem comparison_existsUnique (R : Sheaf J CommRingCat.{max u v r})
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    ∃! a : tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L) ⟶
      tensorFixed.{u, v, r} J R ((coefficientHomResolution.{r, u, v} J R).obj L) ⋙
        homFixed.{u, v, r} J R P,
      Normalized.{u, v, r} J R P L a
```

Original file options:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

There were no additional monoidal proof-context commands after `Normalized`.

## New

The declaration signature is unchanged, verbatim:

```lean
theorem comparison_existsUnique (R : Sheaf J CommRingCat.{max u v r})
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    ∃! a : tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L) ⟶
      tensorFixed.{u, v, r} J R ((coefficientHomResolution.{r, u, v} J R).obj L) ⋙
        homFixed.{u, v, r} J R P,
      Normalized.{u, v, r} J R P L a
```

The original file options remain. The following additional commands occur in the
private proof development (with theorem-scoped transparency options where needed):

```lean
open CategoryTheory.MonoidalCategory
set_option backward.isDefEq.respectTransparency true
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] homComplexFunctor SheafOfModules.monoidalCategory
  PresheafOfModules.sheafification PresheafOfModules.sheafificationAdjunction
attribute [local irreducible] singleTensorIso
attribute [local irreducible] pure
attribute [local irreducible] strengthSection strengthBilinear strengthRaw strength
attribute [local irreducible] homValue
attribute [local irreducible] tensorGenerator
attribute [local irreducible] tensor
```

The theorem is now proved by sheafified pure-tensor evaluation, Hom-product projections,
the degree-zero single-tensor comparison, and the fixed resolution augmentation.
General adjunction lemmas avoid unfolding the concrete localization construction in
routine naturality and cancellation calculations. All new helper declarations are
private and proved. The only added import is the private proof import
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`.

## Users

`tools/downstream.py Sheaf.Paper.DerivedInternalHomFilteredColimitData --uses
WeilConjectures.SfbHomFilteredColimit.comparison_existsUnique` lists the following 61
transitive consumers, plus the assigned module. Its textual declaration search finds
only the assigned module and `Sheaf.Paper.InternalHomFiniteFreeStage`. The table records
claim holders in the current checkout. No consumer is edited, and no target meaning
or unit route is changed; no target statement review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.DerivedInternalHomFilteredColimitData` | K3 | Assigned proof completed; signature and definitions unchanged. |
| `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.CategoryTheory.ThreeStepAdjunctionComparison` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.BoundedConstructibleBaseChange` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.BoundedConstructiblePushforwardRestriction` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.BoundedExchangeAmbient` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.CoefficientDerivedFunctorAPI` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.CoefficientFiniteDescentObjects` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.CoefficientHeartClosure` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.CondensedConstructibleOneStep` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.CondensedConstructibleOpenClosedImages` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.CondensedFiniteCoefficientLocalization` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.CondensedLocallyClosedOneStep` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.CondensedOpenClosedRecollement` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.CondensedPointCoefficients` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.CondensedPointDiscreteConstantComparison` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.ConstantToContinuousScalarFlat` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.ContinuousIntegralComparisons` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.DerivedInternalHomFilteredColimit` | R3 | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.FiniteConstantModelResolution` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.FiniteDiscreteCoefficientEncoding` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.FiniteDiscreteRealizationFunctor` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.FormalClosedSupportDerived` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.FormalClosedSupportSheaves` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.IntegralModelSurjectiveClosedReflection` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.IntegralResidueExchangeAlgebra` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.InternalHomFilteredContinuity` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.InternalHomFiniteFreeStage` | unclaimed | Direct textual user of comparison_existsUnique; signature unchanged; no adaptation. |
| `Sheaf.Paper.OpenExtensionConstantModelConstructible` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.ProperUnboundedWindowBounded` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Paper.TAdmissibleCoefficientModels` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.SixFunctors.BrownHypothesesAmbient` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection` | unclaimed | No interface or statement change; no adaptation required. |
| `Sheaf.Topology.ProfiniteCondensedRing` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.WeilObject.BoundedConstructible.Defs` | unclaimed | No interface or statement change; no adaptation required. |
| `WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar` | unclaimed | No interface or statement change; no adaptation required. |

## Status

landed 20261021T023314-L-2946918 2026-10-21 (merge of deliver/K3/Sheaf.Paper.DerivedInternalHomFilteredColimitData)
