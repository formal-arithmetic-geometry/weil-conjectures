# WeilConjectures.PurityFiniteSetting.existsUnique_finiteReductionOrientationInputComparison

## Reason

The input-comparison proof must keep the source and target finite coefficient
rings distinct without unfolding their quotient-ring implementations during
category inference. Use proof-scoped local irreducibility attributes on Ring and
Coefficient, retain transparency during backward elaboration, and name the shifted
target category explicitly. The proof's categorical algebra is proved once in the
private helper comparisonOfCharts before concrete substitution. Match the
category-instance proofs cached by DerivedCategoryModule, as the existing
supported-Kummer modules do. The transported root chart is also factored into finiteReductionLineChart in the
new module, avoiding two separately elaborated versions of the same expression.
The existing affine input chart is its specialization. No statement, exported
attribute or mathematical map changes; the sibling import becomes public because
the existing data definition uses its real chart construction.

## Old

The original environment commands, verbatim:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
```

The original chart definition was, verbatim:

```lean
def finiteReductionOrientationInputChart (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))]
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    P.finiteReductionOrientationInput Y ≅
      (P.coefficientUnit (AffineSpace (ULift.{u} (Fin 1)) Y))⟦(2 : ℤ)⟧ :=
  let L := AffineSpace (ULift.{u} (Fin 1)) Y
  letI := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring L
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) L).mapDerivedCategory
  let E := (Scheme.sfIntrinsicModuleEquivalence L P.Ring).functor.mapDerivedCategory
  E.mapIso (F.mapIso (P.finiteReductionShiftedLineChart L ζ hζ) ≪≫
    (F.commShiftIso (2 : ℤ)).app (Etale.ordinaryFiniteUnit P.Coefficient L)) ≪≫
    (E.commShiftIso (2 : ℤ)).app (F.obj (Etale.ordinaryFiniteUnit P.Coefficient L))
```

The original theorem proof was exactly:

```lean
:= by
  sorry
```

## New

The original global options remain. Universe variables v and w are used only by
the proved private categorical helper. Immediately around the unchanged theorem
declaration a section scopes these commands:

```lean
section InputComparison
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] PurityFiniteSetting.Ring PurityFiniteSetting.Coefficient
```

The section ends before finiteReductionOrientationInputComparison. Ring and
Coefficient retain their bodies, visibility and exported reducibility. The theorem
now has a complete construction from the scalar chart-change lemma and the
existing scalar-unit comparison; its signature is verbatim. The chosen comparison
has precisely its original unique normalization.

The new chart construction and the replacement body are:

```lean
def finiteReductionLineChart (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    (Scheme.sfIntrinsicDerivedEquivalence T P.Ring).functor.obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
          ((Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)) ≅
      (P.coefficientUnit T)⟦(2 : ℤ)⟧ :=
  letI := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring T
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory
  let E := (Scheme.sfIntrinsicModuleEquivalence T P.Ring).functor.mapDerivedCategory
  E.mapIso (F.mapIso (P.finiteReductionShiftedLineChart T ζ hζ) ≪≫
    (F.commShiftIso (2 : ℤ)).app (Etale.ordinaryFiniteUnit P.Coefficient T)) ≪≫
    (E.commShiftIso (2 : ℤ)).app (F.obj (Etale.ordinaryFiniteUnit P.Coefficient T))

```

```lean
def finiteReductionOrientationInputChart (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))]
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    P.finiteReductionOrientationInput Y ≅
      (P.coefficientUnit (AffineSpace (ULift.{u} (Fin 1)) Y))⟦(2 : ℤ)⟧ :=
  P.finiteReductionLineChart (AffineSpace (ULift.{u} (Fin 1)) Y) ζ hζ

```

Unfolding finiteReductionLineChart gives exactly the old body, with T specialized
to AffineSpace (ULift (Fin 1)) Y and the old let-bound L replaced by that value.
Thus the definition is unchanged up to definitional equality. No target changes
meaning. The new sibling's public import is required by this data body.

Within InputComparison, the local instances
Etale.DerivedCategoryModule._proof_1 and _proof_2 have priority 100000, matching
the existing supported-Kummer modules. These are proofs of HasSheafify and
IsGrothendieckAbelian, and the change alters no data or exported instance.

## Users

`tools/downstream.py Sheaf.Paper.FiniteReductionAffineOrientation --uses
existsUnique_finiteReductionOrientationInputComparison` and
`--uses finiteReductionOrientationInputChart` found 37 downstream modules. Both
declarations have textual users only in the item itself, where the input
comparison continues to choose the uniquely characterized isomorphism. No downstream module
requires adaptation; no holder's source is edited. The table lists every computed
consumer, with holders not queried because no consumer is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteReductionAffineOrientation | A4 | Completed proof; chart data factored with identical signature and map. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.FiniteSupportedReductionEquation | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | not queried; untouched | Identical statements and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | not queried; untouched | Identical statements and definitions; no adaptation. |

| Sheaf.Paper.RationalExceptionalFinalEquations | not queried; untouched | Definitionally identical chart; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | not queried; untouched | Definitionally identical chart; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | not queried; untouched | Definitionally identical chart; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | not queried; untouched | Definitionally identical chart; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | not queried; untouched | Definitionally identical chart; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | not queried; untouched | Definitionally identical chart; no adaptation. |

## Status

landed 20261025T142747-L-753947 2026-10-25 (merge of deliver/A4/Sheaf.Paper.FiniteReductionAffineOrientation)
