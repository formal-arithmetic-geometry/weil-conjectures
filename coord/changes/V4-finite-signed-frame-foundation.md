# FiniteTensorLineFrame and finite signed frame sections

## Reason

The ordinary product proof needs three independent local sheaf steps. They must
refer to the published coherent frames and section maps before the product exists.
Relocate the five foundational declarations unchanged to
`Sheaf.Paper.FiniteTensorProductFrameExt`, which the original module publicly imports.
This removes the prospective proof import cycle. There is one definition of each
notion. No type, body, universe, visibility, target, or mathematical meaning changes.
The original module retains its existing public imports as a compatibility interface.

## Old

Defined in `Sheaf.Paper.FiniteSignedTwistProducts`:

```lean
/-- A coherent signed frame, formed before specializing the coefficient ring or line.
Positive bases are ordered tensors; negative bases evaluate to one.
Source: blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
structure FiniteTensorLineFrame (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (L : proEtaleRingModules T R) (V : T.ProEt) where
  basis : ∀ r : ℤ, Module.Basis (Fin 1) (R.obj.obj (Opposite.op V))
    ((coefficientTwistLine T L r).val.obj (Opposite.op V))
  zero : basis 0 0 = (1 : R.obj.obj (Opposite.op V))
  positive : ∀ j : ℕ, basis (j + 2) 0 =
    SheafOfModules.siteSheafTensorTmul (A := R)
      (coefficientTwistLine T L (j + 1)) L (Opposite.op V)
      (basis (j + 1) 0) (basis 1 0)
  negative : ∀ j : ℕ,
    ((basis (Int.negSucc j) 0).app (Opposite.op (Over.mk (𝟙 V)))) (basis (j + 1) 0) =
      (1 : R.obj.obj (Opposite.op V))

/-- The coherent frame of exactly the prescribed integral-reduced finite line.
Source: blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
abbrev FiniteTensorFrame (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (V : T.ProEt) :=
  FiniteTensorLineFrame T (proEtaleConstantRing T P.Ring) (P.finiteTensorFirstLine T) V

/-- The basis vector of a coherent signed frame, with its section module fixed.
Source: blueprint proof Steps 5 and 8
(blueprint: def-pur-finite-signed-twist-products). -/
def finiteTensorFrameBasis (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (V : T.ProEt)
    (b : P.FiniteTensorFrame T V) (r : ℤ) :
    (P.finiteTensorLine T r).val.obj (Opposite.op V) :=
  b.basis r 0

/-- The canonical local-section realization, using its scalar unit and counit.
Source: Stacks 00YV, blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
def finiteTensorSection (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (r : ℤ)
    (V : T.ProEt) (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V)) :=
  ((sfIntrinsicModuleEquivalence T P.Ring).counitIso.hom.app
    (P.finiteTensorLine T r)).val.app (Opposite.op V)
      (sfIntrinsicRealizationUnit T P.Ring (P.finiteTensorFixedSheaf T r) (Opposite.op V) x)

/-- The ordinary sheaf pure tensor, before passing to degree-zero complexes.
Source: Stacks 03EK, blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
def finiteTensorSectionTmul (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (r t : ℤ)
    (V : T.ProEt) (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V))
    (y : (P.finiteTensorFixedSheaf T t).obj.obj (Opposite.op V)) :=
  (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} P.Coefficient))
      (P.finiteTensorFixedSheaf T r) (P.finiteTensorFixedSheaf T t)).app (Opposite.op V)
        (x ⊗ₜ[P.Coefficient] y)

```

## New

The same declarations and bodies, verbatim, now reside in
`Sheaf.Paper.FiniteTensorProductFrameExt`:

```lean
/-- A coherent signed frame, formed before specializing the coefficient ring or line.
Positive bases are ordered tensors; negative bases evaluate to one.
Source: blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
structure FiniteTensorLineFrame (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (L : proEtaleRingModules T R) (V : T.ProEt) where
  basis : ∀ r : ℤ, Module.Basis (Fin 1) (R.obj.obj (Opposite.op V))
    ((coefficientTwistLine T L r).val.obj (Opposite.op V))
  zero : basis 0 0 = (1 : R.obj.obj (Opposite.op V))
  positive : ∀ j : ℕ, basis (j + 2) 0 =
    SheafOfModules.siteSheafTensorTmul (A := R)
      (coefficientTwistLine T L (j + 1)) L (Opposite.op V)
      (basis (j + 1) 0) (basis 1 0)
  negative : ∀ j : ℕ,
    ((basis (Int.negSucc j) 0).app (Opposite.op (Over.mk (𝟙 V)))) (basis (j + 1) 0) =
      (1 : R.obj.obj (Opposite.op V))

/-- The coherent frame of exactly the prescribed integral-reduced finite line.
Source: blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
abbrev FiniteTensorFrame (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (V : T.ProEt) :=
  FiniteTensorLineFrame T (proEtaleConstantRing T P.Ring) (P.finiteTensorFirstLine T) V

/-- The basis vector of a coherent signed frame, with its section module fixed.
Source: blueprint proof Steps 5 and 8
(blueprint: def-pur-finite-signed-twist-products). -/
def finiteTensorFrameBasis (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (V : T.ProEt)
    (b : P.FiniteTensorFrame T V) (r : ℤ) :
    (P.finiteTensorLine T r).val.obj (Opposite.op V) :=
  b.basis r 0

/-- The canonical local-section realization, using its scalar unit and counit.
Source: Stacks 00YV, blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
def finiteTensorSection (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (r : ℤ)
    (V : T.ProEt) (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V)) :=
  ((sfIntrinsicModuleEquivalence T P.Ring).counitIso.hom.app
    (P.finiteTensorLine T r)).val.app (Opposite.op V)
      (sfIntrinsicRealizationUnit T P.Ring (P.finiteTensorFixedSheaf T r) (Opposite.op V) x)

/-- The ordinary sheaf pure tensor, before passing to degree-zero complexes.
Source: Stacks 03EK, blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
def finiteTensorSectionTmul (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (r t : ℤ)
    (V : T.ProEt) (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V))
    (y : (P.finiteTensorFixedSheaf T t).obj.obj (Opposite.op V)) :=
  (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} P.Coefficient))
      (P.finiteTensorFixedSheaf T r) (P.finiteTensorFixedSheaf T t)).app (Opposite.op V)
        (x ⊗ₜ[P.Coefficient] y)

```

The original module publicly imports that module. The new module adds the tensor
frame detection theorem. The two other new modules add only the separate normalized
morphism-existence and local-invertibility theorems. They are private proof imports
of the item. All preexisting consumers continue to see the original public names.
No consumer statement becomes stronger or weaker, and no target review is reopened:
the definitions have exactly the same bodies.

## Users

The table includes all 46 transitive importers reported by downstream.py, covering
its direct users of the five relocated declarations as well as all six direct importers.
No consumer requires a source adaptation. Claims below are from the shared snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.FinitePositiveChartFrameExt | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.FinitePositiveChartRecursion | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.FinitePositiveRootChartPower | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.FinitePositiveRootCharts | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | S3 | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionReassociation | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorSource | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorPresentationReduction | M7 | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | S2 | Identical public names and bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Identical public names and bodies through public reexport; no adaptation. |

## Status

landed 20261025T181238-L-4122249 2026-10-25 (merge of deliver/V4/Sheaf.Paper.FiniteSignedTwistProducts)
