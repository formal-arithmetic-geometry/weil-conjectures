# AlgebraicGeometry.ConormalGradedAlgebra: relocation of the fixed pieces

## Reason

Move the six existing definitions into `ConormalGradedAlgebraBasic` so that the
construction and stalk lemmas can use the fixed pieces without importing the
existence theorem and creating an import cycle. `ConormalGradedAlgebra` publicly
imports this basic module. All six declaration names, signatures, visibility and
bodies are preserved verbatim; the definitions and target meanings do not change.
The `Presentation` structure and all existing theorem and definition signatures
in the item are unchanged. No source-library declaration is edited.

## Old

In `lean/Sheaf/AlgebraicGeometry/ConormalGradedAlgebra.lean`, under its existing
namespace and variables:

```lean
def power (n : ℕ) : X.Modules :=
  (Scheme.idealSheafPower i.ker.toModulesι n).1

def powerInclusion (n : ℕ) : power i n ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.idealSheafPower i.ker.toModulesι n).2

def piece (n : ℕ) : Z.Modules := (Scheme.Modules.tensorPullback i).obj (power i n)

def representative (n : ℕ) (U : X.Opens) (a : (power i n).val.obj (op U)) :
    (piece i n).val.obj (op (i ⁻¹ᵁ U)) :=
  ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
    (power i n)).val.app (op U) a

def homogeneousClass (A : Z.CommAlgebraSheaf) (j : ∀ n, piece i n ⟶ A.toModule)
    (n : ℕ) (U : X.Opens) (a : (power i n).val.obj (op U)) :
    A.right.obj.obj (op (i ⁻¹ᵁ U)) :=
  (j n).val.app (op (i ⁻¹ᵁ U)) (representative i n U a)

def quotientStalk (z : Z) :
    X.presheaf.stalk (i z) ⧸ RingHom.ker (i.stalkMap z).hom ≃+* Z.presheaf.stalk z :=
  RingHom.quotientKerEquivOfSurjective (i.stalkMap_surjective z)
```

## New

In `lean/Sheaf/AlgebraicGeometry/ConormalGradedAlgebraBasic.lean`, under the same
namespace and variables, publicly re-exported by the original module:

```lean
def power (n : ℕ) : X.Modules :=
  (Scheme.idealSheafPower i.ker.toModulesι n).1

def powerInclusion (n : ℕ) : power i n ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.idealSheafPower i.ker.toModulesι n).2

def piece (n : ℕ) : Z.Modules := (Scheme.Modules.tensorPullback i).obj (power i n)

def representative (n : ℕ) (U : X.Opens) (a : (power i n).val.obj (op U)) :
    (piece i n).val.obj (op (i ⁻¹ᵁ U)) :=
  ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
    (power i n)).val.app (op U) a

def homogeneousClass (A : Z.CommAlgebraSheaf) (j : ∀ n, piece i n ⟶ A.toModule)
    (n : ℕ) (U : X.Opens) (a : (power i n).val.obj (op U)) :
    A.right.obj.obj (op (i ⁻¹ᵁ U)) :=
  (j n).val.app (op (i ⁻¹ᵁ U)) (representative i n U a)

def quotientStalk (z : Z) :
    X.presheaf.stalk (i z) ⧸ RingHom.ker (i.stalkMap z).hom ≃+* Z.presheaf.stalk z :=
  RingHom.quotientKerEquivOfSurjective (i.stalkMap_surjective z)
```

## Users

The table includes every module listed by `tools/downstream.py` for the namespace,
including the indirect importers with no direct use. Since the declaration bodies
are identical, none of their statements changes in strength or meaning. The target
statements and their definitions are unchanged. The normalized representative and
quotient-stalk definitions are used directly in the new proved lemmas.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ConormalAlgebraAffineGenerators` | unclaimed | Uses `power`, `powerInclusion` and `homogeneousClass` through the original module's public re-export. All six relocated definitions retain their names, signatures, visibility and bodies; no adaptation or statement change. |
| `Sheaf.AlgebraicGeometry.ConormalAlgebraHomogeneousRingMap` | unclaimed | Uses `power`, `powerInclusion` and `homogeneousClass` through the original module's public re-export. All six relocated definitions retain their names, signatures, visibility and bodies; no adaptation or statement change. |
| `Sheaf.AlgebraicGeometry.ConormalAlgebraRingAdjoint` | unclaimed | Uses `power`, `powerInclusion` and `homogeneousClass` through the original module's public re-export. All six relocated definitions retain their names, signatures, visibility and bodies; no adaptation or statement change. |
| `Sheaf.AlgebraicGeometry.ConormalAlgebraFlatBaseChange` | F8 | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.AlgebraicGeometry.ConormalConeHomExt` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.AlgebraicGeometry.ConormalConeZeroSectionPullback` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.AlgebraicGeometry.ConormalGradedAlgebra` | N2 | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.AlgebraicGeometry.ConormalGradedAlgebraHomExt` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.AlgebraicGeometry.ReesConeNormalization` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.AlgebraicGeometry.ReesConeNormalizedExistence` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.CompactSupportPerfectness` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.DerivedGeometricStalk` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteRingSectionDeformation` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteSmoothAdjunctionData` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteSmoothCanonicalInterfaces` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteSmoothCoefficientArrows` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteSmoothGammaNormalization` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteSmoothLevelOfOrientation` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteSmoothPurityMaps` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteSmoothQuotientCoherence` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteSmoothSiteRealizations` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteSmoothTwoLevelReduction` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.NoetherianEtaleSectionSpecialization` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.PurityConventions` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.PurityDiagonalOrientationCompatibility` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.PurityDncComparisons` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.PurityDncInvariance` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.PurityExteriorProductFrame` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.PurityNormalBundle` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.PurityNormalCone` | H3 | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.PurityTwistCancellation` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.SupportedExteriorClasses` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | Existing names, signatures, visibility and definition bodies are unchanged; the original module publicly re-exports the relocated definitions. No adaptation. |

## Status

landed 20261020T233205-L-904241 2026-10-20 (merge of deliver/N2/Sheaf.AlgebraicGeometry.ConormalGradedAlgebra)
