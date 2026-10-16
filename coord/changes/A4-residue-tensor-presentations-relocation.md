# residueExchangeCoefficientPullIso and residueExchangeTensorPullIso

## Reason

Move these unchanged constructions to IntegralResidueTensorPullPresentation so the
independent route-computation modules can use them before Geometry combines their
conclusions. Keeping the definitions in Geometry would create an import cycle.
This relocation is not a timeout split. No target statement or definition data changes.

## Old

In lean/Sheaf/Paper/IntegralResidueTensorGeometry.lean:

```lean
@[irreducible] noncomputable def residueExchangeCoefficientPullIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
        (residueExchangeCoefficient ℓ E Y) ≅ residueExchangeCoefficient ℓ E X := by
  let A := Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)
  let P := Mod.regular (condensedRingObj A Y)
  let SY := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (coefficientMap (integralReductionMap ℓ E) Y)
  let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (integralReductionMap ℓ E) X)
  letI := residueOrdinaryUpperStarMonoidal A f
  let e : (f)^*⟦integralCoeff ℓ E⟧.obj (SY.obj P) ≅
      SX.obj (Mod.regular (condensedRingObj A X)) :=
    (comapUpperStarIso (integralReductionMap ℓ E) f).symm.app P ≪≫
      SX.mapIso (Functor.Monoidal.εIso (f)^*⟦A⟧).symm
  unfold residueExchangeUpperStar
  exact ((f)^*⟦integralCoeff ℓ E⟧.singleFunctorCompLeftDerivedFunctorIso).app (SY.obj P) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e

/-- The tensor presentation on X, with its coefficient identified with pullback from Y. -/
@[irreducible] noncomputable def residueExchangeTensorPullIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeReduction ℓ E X ⋙ residueExchangeRestriction ℓ E X ≅
      tensorRight ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj
        (residueExchangeCoefficient ℓ E Y)) :=
  residueExchangeTensorIso ℓ E X ≪≫
    (curriedTensor (residueExchangeDerived (integralCoeff ℓ E) X)).flip.mapIso
      (residueExchangeCoefficientPullIso ℓ E f).symm
```

## New

The same declarations in lean/Sheaf/Paper/IntegralResidueTensorPullPresentation.lean,
publicly re-exported by their original module:

```lean
@[irreducible] noncomputable def residueExchangeCoefficientPullIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
        (residueExchangeCoefficient ℓ E Y) ≅ residueExchangeCoefficient ℓ E X := by
  let A := Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)
  let P := Mod.regular (condensedRingObj A Y)
  let SY := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (coefficientMap (integralReductionMap ℓ E) Y)
  let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (integralReductionMap ℓ E) X)
  letI := residueOrdinaryUpperStarMonoidal A f
  let e : (f)^*⟦integralCoeff ℓ E⟧.obj (SY.obj P) ≅
      SX.obj (Mod.regular (condensedRingObj A X)) :=
    (comapUpperStarIso (integralReductionMap ℓ E) f).symm.app P ≪≫
      SX.mapIso (Functor.Monoidal.εIso (f)^*⟦A⟧).symm
  unfold residueExchangeUpperStar
  exact ((f)^*⟦integralCoeff ℓ E⟧.singleFunctorCompLeftDerivedFunctorIso).app (SY.obj P) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e

/-- The tensor presentation on X, with its coefficient identified with pullback from Y.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: def-weil-pbc-integral-residue-tensor-pull-presentation) -/
@[irreducible] noncomputable def residueExchangeTensorPullIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeReduction ℓ E X ⋙ residueExchangeRestriction ℓ E X ≅
      tensorRight ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj
        (residueExchangeCoefficient ℓ E Y)) :=
  residueExchangeTensorIso ℓ E X ≪≫
    (curriedTensor (residueExchangeDerived (integralCoeff ℓ E) X)).flip.mapIso
      (residueExchangeCoefficientPullIso ℓ E f).symm
```

## Users

Both `tools/downstream.py --uses` queries were run. The coefficient isomorphism has
no external textual consumer; the tensor isomorphism is used by TensorSquare.
All twelve downstream modules are listed below. The original theorem signature
is byte-for-byte unchanged; the construction bodies and signatures were compared
after stripping docstrings. Their meaning is unchanged, so this relocation does
not reopen target-statement review. The unchanged direct textual consumer
Sheaf.Paper.IntegralResidueTensorSquare was compiled successfully against the overlay.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralResidueTensorGeometry | A4 | Public re-export and proof from the two computation formulas. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Identical names, signatures, visibility and data through public re-export; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Identical names, signatures, visibility and data through public re-export; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Identical names, signatures, visibility and data through public re-export; no adaptation. |
| Sheaf.Paper.IntegralResidueComparisons | unclaimed | Identical names, signatures, visibility and data through public re-export; no adaptation. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Identical names, signatures, visibility and data through public re-export; no adaptation. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Identical names, signatures, visibility and data through public re-export; no adaptation. |
| Sheaf.Paper.IntegralResidueProjectionNormalization | unclaimed | Identical names, signatures, visibility and data through public re-export; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorSquare | unclaimed | Identical names, signatures, visibility and data through public re-export; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Identical names, signatures, visibility and data through public re-export; no adaptation. |
| TargetsCheck | unclaimed | Identical names, signatures, visibility and data through public re-export; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Identical names, signatures, visibility and data through public re-export; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Identical names, signatures, visibility and data through public re-export; no adaptation. |

## Status

landed 20261016T134405-L-3314624 2026-10-16 (merge of deliver/A4/Sheaf.Paper.IntegralResidueTensorGeometry)
