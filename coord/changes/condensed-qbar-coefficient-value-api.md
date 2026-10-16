# Condensed Qbar coefficient scalar-value API and common constructions

## Reason

The original four-property theorem now has a complete Lean proof from two independent
compatibility obligations. Those obligations must refer to the actual constructed data.
Keeping those data in the item while importing their new proof modules would make an
import cycle. The pre-existing construction section therefore moves verbatim to
`Sheaf.Paper.CondensedQbarCoefficientConstruction`, which the original module publicly
imports. Public names, universes, signatures, values and visibility of every moved
declaration stay identical; only their module and blueprint attachment change.

Kernel checking of the old scalar-coordinate field expanded the geometric inverse-image
module construction even when the same fiber and coordinates occurred on both sides.
Introduce `regularScalarValue` as the exact old value expression, with a proved computation
rule, and state the two scalar-value fields through it. This is a definitionally identical
proposition, without a new assumption or a weaker conclusion. This repair was tested in
the complete unsplit file: all new proofs compiled in 34 seconds before the data moved.
The move is for independent imports, not to evade the 60-second limit.

No definition of a geometric fiber, regular coordinates, scalar action, coefficient
realization, or target statement changes. All objects remain actual constructions;
no data are chosen from a merely existential unproved assertion. No unit realization
is bypassed. No target statement directly uses the folded helper, and its exact
computation rule proves that the meaning of any indirect use is unchanged.

## Old

The construction section (all declarations from `CondensedQbarCoefficientRealization`
through `CondensedQbarGeometricEvaluation`) lived in
`Sheaf.Paper.CondensedQbarFunctionCoefficients`. Its existing public declarations are
moved with exactly the same signatures and bodies. The scalar fields were:

In `CondensedQbarCoefficientProperties`:

```lean
  fiber_scalar (U : X.ProEt) (x : U.left)
      (a : PadicAlgCl.finiteIntermediateFieldValued ℓ U.left) :
    (d.fiber_regular U x)
      ((d.fiber U x).map
      (condensedQbarScalar ℓ U.left a)
        ((d.fiber_regular U x).symm 1)) = a.1 x
```

In `CondensedQbarFunctionCoefficients`:

```lean
  fiber_scalar (U : X.ProEt) (x : U.left)
      (a : PadicAlgCl.finiteIntermediateFieldValued ℓ U.left) :
    fiber_regular U x ((fiber U x).map
      (condensedQbarScalar ℓ U.left a)
        ((fiber_regular U x).symm 1)) = a.1 x
```

## New

The original module publicly imports the common construction module:

```lean
public import Sheaf.Paper.CondensedQbarCoefficientConstruction
```

The lower module contains all original construction declarations and this actual value
operation and computation rule:

```lean
noncomputable def regularScalarValue
    {R : Type w} [CommRing R] {C : Type v} [Category.{z} C]
    (F : C ⥤ ModuleCat.{u} R) {A : C} (c : F.obj A ≃ₗ[R] R) (f : A ⟶ A) : R :=
  c (F.map f (c.symm 1))

/-- Computation rule for the folded regular scalar value.
Source: RefactorInstruction, Section 4, geometric scalar evaluation
(blueprint: def-weil-pbc-condensed-qbar-coefficient-construction). -/
lemma regularScalarValue_def
    {R : Type w} [CommRing R] {C : Type v} [Category.{z} C]
    (F : C ⥤ ModuleCat.{u} R) {A : C} (c : F.obj A ≃ₗ[R] R) (f : A ⟶ A) :
    regularScalarValue F c f = c (F.map f (c.symm 1)) := by
  unfold regularScalarValue
  rfl
```

The two field signatures now use that same value operation:

In `CondensedQbarCoefficientProperties`:

```lean
  fiber_scalar (U : X.ProEt) (x : U.left)
      (a : PadicAlgCl.finiteIntermediateFieldValued ℓ U.left) :
    regularScalarValue (d.fiber U x) (d.fiber_regular U x)
      (condensedQbarScalar ℓ U.left a) = a.1 x
```

In `CondensedQbarFunctionCoefficients`:

```lean
  fiber_scalar (U : X.ProEt) (x : U.left)
      (a : PadicAlgCl.finiteIntermediateFieldValued ℓ U.left) :
    regularScalarValue (fiber U x) (fiber_regular U x)
      (condensedQbarScalar ℓ U.left a) = a.1 x
```

The item imports `CondensedQbarScalarPullback` and `CondensedQbarFieldFiberExtension`
only for proofs. Those modules publicly import the common data module, without
importing the item. The original coefficient-property theorem and existence theorem
retain their signatures exactly. The original structure's other fields, including
fiber comparison and weakly etale scalar restriction, are unchanged. All consumers
still import the original module and see the same explicit definitions transitively.

## Users

`tools/downstream.py` was run for the moved construction names and for `fiber_scalar`.
Only the item itself uses the concrete geometric functor and coordinate declarations.
`CondensedQbarLfpMatrixRefinement` also uses `globalCoefficientIso`;
`CondensedQbarFunctionPresentations` uses the regular pullback comparison and the
scalar-value property. All transitive consumers reported by the tool are listed below.
The public import keeps the moved names available. The value field is definitionally
the previous expression by `regularScalarValue_def`.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CondensedQbarFunctionCoefficients` | B3 | Prove the original theorem; fold scalar-value fields; publicly re-export moved constructions. |
| `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedFiniteModelExtensions` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedFiniteModelProofAPI` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedLfpHomContinuity` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedLocalPieceHomContinuity` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedQbarFunctionPresentations` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedQbarLfpLocalTriviality` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedQbarLfpMatrixRefinement` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedSheafExtContinuity` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedStratumModelAssembly` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedStratumModelInductionStep` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedStratumModelInductionStepEmpty` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonempty` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ConstructibleCokernelsExtensions` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralDenominators` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralGluing` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralImage` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralModel` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralSingle` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralStratum` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousExchangeIntegralModel` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousFiniteFreeKernelModel` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralComplexTelescope` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralExchangeSquare` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalization` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationContinuity` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationCounit` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationHomology` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationLegs` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationMate` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationModel` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralModuleTelescope` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralPushComparison` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralRegularTelescope` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralUnderivedPushComparison` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousLatticeIntersectionLocalModel` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousLatticeIntersectionRationalModel` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousLatticeIntersectionRationalization` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousLatticeIntersectionSplitData` | B2 | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousLatticeIntersectionSplitModel` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.ContinuousLisseStratifiedLattices` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.IntegralConstructibleKernels` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.IntegralConstructibleNakayama` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.IntegralConstructibleSequentialHom` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.IntegralConstructibleSerre` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.IntegralConstructibleSheafHom` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.IntegralExchangeReduction` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.IntegralFiniteExchangeComparison` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.IntegralLfpEventualFreeImage` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.IntegralLfpFiniteQuotientCharts` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.IntegralLfpHomContinuity` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.IntegralLfpLocalTorsionCharts` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.IntegralLfpLocallyFreeResolution` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.IntegralMatrixKernelLocallyFree` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.IntegralReductionConservative` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.IntegralReductionConstructible` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.IntegralResidueExchange` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `TargetsCheck` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | unclaimed | Same constructions and definitionally identical scalar-value property; no source adaptation. |
| `Sheaf.Paper.CondensedQbarCoefficientConstruction` | B3 (new module) | Common explicit data or independent compatibility obligation. |
| `Sheaf.Paper.CondensedQbarScalarPullback` | B3 (new module) | Common explicit data or independent compatibility obligation. |
| `Sheaf.Paper.CondensedQbarFieldFiberExtension` | B3 (new module) | Common explicit data or independent compatibility obligation. |
| `Sheaf.Paper.CondensedQbarFieldEvaluationLinearity` | B3 (new module) | Common explicit data or independent compatibility obligation. |

## Status

landed 20261016T103838-L-2369259 2026-10-16 (merge of deliver/B3/Sheaf.Paper.CondensedQbarFunctionCoefficients)
