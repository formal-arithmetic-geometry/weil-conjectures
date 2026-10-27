# WeilConjectures.PurityFiniteSetting.finiteReductionEtaleOrientation

## Reason

A compile with the completed comparison proof had no Lean errors but took 73.8 seconds;
another took 88.6 seconds. A profiler run passed at 47.0 seconds. Detailed profiler tracing
then identified the existing finiteReductionEtaleOrientation kernel check (33.5 seconds)
and its generated _proof_15 (9.65 seconds) as large costs before the new proof is reached.
The generated derived-category structures unfold different instance expressions.
Reuse DerivedCategoryModule's cached HasSheafify and IsGrothendieckAbelian proof instances,
with exactly the same local priorities already used in section InputComparison. Retain
backward elaboration transparency and locally protect Ring and Coefficient from unfolding.
The remaining HasExt instance kernel check still made the compile exceed 60 seconds.
Factor the same supported-class adjunct expression into the public generic helper
finiteReductionSupportedOrientationAdjunct, with its HasExt proof as a parameter, and specialize it to P.Coefficient, the zero
section and the uniquely specified Kummer class. This is a transparent definition with
exactly the original expression as its body; it chooses no new data. The helper is attached
to the same existing definition node. The section ends after the specialized definition;
later declarations retain their context. Existing signatures and mathematical maps stay
identical, and no exported attribute is changed.

## Old

The declaration below was elaborated in the existing global environment, with
`set_option backward.isDefEq.respectTransparency false` and no local cached-instance override:

```lean
def finiteReductionEtaleOrientation (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))] :
    Etale.ordinaryFiniteUnit P.Coefficient Y ⟶
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).obj
          ((Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates
            (AffineSpace (ULift.{u} (Fin 1)) Y))⟦(2 : ℤ)⟧) :=
  let s := AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y
  ((Etale.rightDerivedUpperShriekAdjunction
    (ModuleCat.{u + 1} P.Coefficient) s).homEquiv _ _)
      (((Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} P.Coefficient) s).app
            (Etale.ordinaryFiniteUnit P.Coefficient Y)).hom ≫
        Etale.supportedExactDerivedMap
          (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) s)
          (Etale.ordinaryFiniteConstant P.Coefficient Y)
          (Scheme.finiteEtaleTateLine (AffineSpace (ULift.{u} (Fin 1)) Y)
            P.diagonalExponent P.Coefficient P.diagonalExponent_annihilates)
          (P.existsUnique_finiteReductionOrientationClass Y).choose)
```

## New

The existing declaration keeps its signature and docstring. The generic helper and
specialization, with the scoped instance context, are:

```lean
section EtaleOrientation
-- Reuse the category instances in the ordinary derived category throughout the adjunct.
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] PurityFiniteSetting.Ring PurityFiniteSetting.Coefficient

/-- The exceptional adjunct of an ordinary supported degree-two class.
This is the same direct-image comparison and exact Ext realization used by the affine
orientation, with the coefficient ring and immersion kept as parameters.
Source: blueprint Step 3, supported Kummer orientation
(blueprint: def-pur-finite-affine-orientation-comparison). -/
def finiteReductionSupportedOrientationAdjunct
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    [CategoryTheory.HasExt.{u + 1}
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))]
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (κ : CategoryTheory.Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
        (Etale.ordinaryFiniteConstant A D)) M 2) :
    Etale.ordinaryFiniteUnit A D ⟶
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) i).obj
        (((_root_.DerivedCategory.singleFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj M)⟦(2 : ℤ)⟧) :=
  ((Etale.rightDerivedUpperShriekAdjunction
    (ModuleCat.{u + 1} A) i).homEquiv _ _)
      (((Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) i).app
            (Etale.ordinaryFiniteUnit A D)).hom ≫
        Etale.supportedExactDerivedMap (Etale.lowerStar (ModuleCat.{u + 1} A) i)
          (Etale.ordinaryFiniteConstant A D) M κ)

/-- Ordinary affine-line orientation, as the exceptional adjunct of the supported
coordinate boundary. Source: blueprint Step 3; Stacks 03PL, 0A45
(blueprint: def-pur-finite-affine-orientation-comparison). -/
def finiteReductionEtaleOrientation (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))] :
    Etale.ordinaryFiniteUnit P.Coefficient Y ⟶
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).obj
          ((Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates
            (AffineSpace (ULift.{u} (Fin 1)) Y))⟦(2 : ℤ)⟧) :=
  finiteReductionSupportedOrientationAdjunct P.Coefficient
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)
    (Scheme.finiteEtaleTateLine (AffineSpace (ULift.{u} (Fin 1)) Y)
      P.diagonalExponent P.Coefficient P.diagonalExponent_annihilates)
    (P.existsUnique_finiteReductionOrientationClass Y).choose

end EtaleOrientation

```

Unfold finiteReductionSupportedOrientationAdjunct and substitute its displayed arguments:
its result is the old body above, with the local s let-expanded. The old ordinaryFiniteLine
is the single complex of the displayed finiteEtaleTateLine by definition. Thus the
replacement is definitionally equal to the original map. Only proof-valued instance
arguments change; proof irrelevance identifies these arguments. No target changes meaning.
Public instance tables and reducibility attributes remain identical; no consumer needs
adaptation. The only new public declaration is the real, explicit adjunct construction
under lean/Sheaf, recorded on the existing orientation definition node.

## Users

Computed with tools/downstream.py and --uses finiteReductionEtaleOrientation. The only textual
uses are in the item, including the realization definition finiteReductionOrientation.
All transitive consumers are listed below. None is edited and no holder is queried because
there is no forced consumer adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteReductionAffineOrientation | F9 | Generic adjunct factoring and local definition elaboration context. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.FiniteSupportedReductionEquation | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | not queried; untouched | Identical public interface and map; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | not queried; untouched | Identical public interface and map; no adaptation. |

## Status

landed 20261025T204556-L-2976881 2026-10-25 (merge of deliver/F9/Sheaf.Paper.FiniteReductionAffineOrientation)
