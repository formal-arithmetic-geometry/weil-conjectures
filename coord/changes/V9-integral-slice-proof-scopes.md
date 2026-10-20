# Sheaf.Paper.IntegralDerivedOperationsOnSlices

## Reason

Prove the transition normalization and completion-unit uniqueness without changing any
existing public theorem statement, public import, or instance body. The inferred types
of five definitions are now explicit, with identical exported types.

The public generator uses a named equality proof `reduction_obj` instead of projecting
the complete derived-functor witness. Its private unit-module constructor uses the same
proof. `generator_original_formula` proves by reflexivity equality with the original
public generator formula. The mathematical data and all target meanings are identical.
The new public equation is fully proved and is attached to the existing definition node.
Every other new helper is private and fully proved. The generic categorical and site
whiskering lemmas use the existing K-flat resolution theorem, keeping scheme data out
of the categorical construction. All added reducibility attributes are explicitly local.

The static preflight also classifies new namespace, universe, variable, section and
local attribute commands as interface changes. This record documents their scope.
No consumer requires adaptation.
The generic scalar-extension construction is reused from the already-imported module
`Sheaf.Paper.IntegralReductionTowerUnrestricted` through a private `import all`.
Its private helpers are identical to the initially tested generic construction, and
no duplicate construction is retained in this delivery. The unary whiskering proof also reuses the private resolving-localization and
full essentially-surjective whiskering lemmas through `import all`. Its new proof
and the cone-map helpers have private names. Additional universe names are used only by
these helpers; existing public signatures retain their original universes.
The coefficient transition and its projection compatibility are also reused from that module.
The named reduction equations and degreewise-unit formula avoid repeated unfolding
of chosen normalized data in the generator-map and augmentation proofs.

## Old

The affected public theorem signatures and original proof bodies, verbatim:

```lean
theorem transition_existsUnique (n : ℕ) :
    ∃! τ : level l E X U (n + 1) ⟶ level l E X U n,
      ∀ (P : Cx l E X U) (i : ℤ) (V : (Site X U)ᵒᵖ)
        (s : (finite l E X U (n + 1)).obj.obj V) (x : (P.X i).val.obj V),
        ((τ.app P).f i).val.app V (generator l E X U (n + 1) (P.X i) V s x) =
          generator l E X U n (P.X i) V ((rho l E X U n).hom.app V s) x := by
  sorry

theorem completionUnit_existsUnique :
    ∃! η : 𝟭 (D l E X U) ⟶ completion l E X U,
      ∀ P : (Good l E X U).FullSubcategory,
        η.app ((qGood l E X U).obj P) ≫ (completionComparison l E X U).hom.app P =
          DerivedCategory.Q.map (roosUnit l E X U P.obj) := by
  sorry
```

The original unannotated definitions were:

```lean
def reduction (n : ℕ) := (reductionWitness l E X U n).choose
def transition (n : ℕ) := (transition_existsUnique l E X U n).exists.choose
def augmentation := (augmentation_existsUnique l E X U).exists.choose
def completion := (completion_exists l E X U).choose
def hom := derivedInternalHomOfUniverses.{t + 1, t, u} (topology X U) (ring l E X U)

def completionUnit : 𝟭 (D l E X U) ⟶ completion l E X U :=
  (completionUnit_existsUnique l E X U).exists.choose
```

The original namespace prelude, following the common options and open commands, was:

```lean
namespace WeilConjectures
namespace IntegralOnSlice
```

The original generator cast was:

```lean
(eqToHom ((reductionWitness l E X U n).choose_spec.choose M).symm)
```

## New

The two public signatures in Old are identical. Their proof bodies are complete.
The previously proved generator-map and augmentation arguments are refactored through
proved private equations; their statements stay identical. The generator cast normalization is recorded below.
Their purely categorical existence-and-uniqueness argument is factored into a fully proved
private theorem `normalizedUnit_existsUnique`.

The same definition bodies now have explicit types, to avoid repeated inference of large
functor and transformation types. These are exactly the former inferred types:

```lean
def reduction (n : ℕ) :
    Mod l E X U ⥤ SheafOfModules.{max u (t + 1)}
      (SheafOfModules.derivedChangeRingIndependentCoefficients
        (topology X U) (finite l E X U n)) :=
  (reductionWitness l E X U n).choose

def transition (n : ℕ) : level l E X U (n + 1) ⟶ level l E X U n :=
  (transition_existsUnique l E X U n).exists.choose

def augmentation :
    (Functor.const ℕᵒᵖ : Cx l E X U ⥤ (ℕᵒᵖ ⥤ Cx l E X U)) ⟶ tower l E X U :=
  (augmentation_existsUnique l E X U).exists.choose

def completion : D l E X U ⥤ D l E X U :=
  (completion_exists l E X U).choose

def hom : (D l E X U)ᵒᵖ × D l E X U ⥤ D l E X U :=
  derivedInternalHomOfUniverses.{t + 1, t, u} (topology X U) (ring l E X U)
```

The following scope commands surround the added private helper declarations:

```lean
universe a b c d e f r

namespace WeilConjectures
namespace IntegralOnSlice

attribute [local irreducible] reductionWitness
section TransitionConstruction
attribute [local irreducible] unrestrictedModuleStep
end TransitionConstruction
attribute [local irreducible] levelUnit
attribute [local irreducible] tower augmentation
attribute [local irreducible] completion completionComparison
attribute [local irreducible] roosUnit
```

The `TransitionConstruction` section contains the existing private unit helpers and
the new proved scalar-transition helpers together with the proved public transition
theorem. It ends before the original transition definition. No exported notation,
instance or attribute is added.

Four private proof imports are added. `import all` permits use of the existing private
generic scalar-extension lemmas in this proof and is not a public import:

```lean
import all Sheaf.Paper.IntegralReductionTowerUnrestricted
import all Sheaf.Paper.ResolvingRepresentativeWhiskering
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
```

The same cast now uses the named, proved equality:

```lean
/-- The normalized scalar-extension functor has the prescribed objects.
Source: Stacks 06YY (blueprint: def-pur-integral-derived-operations).
Proof: project the object-normalization clause of the scalar-extension witness. -/
theorem reduction_obj (n : ℕ) (M : Mod l E X U) :
    (reduction l E X U n).obj M =
      SheafOfModules.changeOfRings (projection l E X U n) M :=
  (reductionWitness l E X U n).choose_spec.choose M

-- In generator and the private unitModule:
(eqToHom (reduction_obj l E X U n M).symm)
```

The complete original generator expression is retained in the proved private equation
`generator_original_formula`, whose proof is `rfl`. Thus changing its equality proof
preserves the public data by definitional equality. The new equation has no prior users;
all existing signatures are retained. The generator's statement and source are unchanged.

The completion-unit definition writes its existing choice application explicitly:

```lean
def completionUnit : 𝟭 (D l E X U) ⟶ completion l E X U :=
  Classical.choose (α := 𝟭 (D l E X U) ⟶ completion l E X U)
    (p := fun η ↦ ∀ P : (Good l E X U).FullSubcategory,
      η.app ((qGood l E X U).obj P) ≫ (completionComparison l E X U).hom.app P =
        DerivedCategory.Q.map (roosUnit l E X U P.obj))
    (ExistsUnique.exists (completionUnit_existsUnique l E X U))
```

This expands the original `.exists.choose` field notation to the identical application,
with its implicit type and predicate explicit. It does not change the chosen witness.
The exported Hom type was checked against the original compiled declaration, which
has exactly the original universes `t, u` and the displayed product-functor type.

## Users

The source-only `tools/downstream.py` check lists the following transitive importers.
Its `--uses transition_existsUnique completionUnit_existsUnique` search finds each
name only in the item module itself. Every importer retains the same public statements,
data and instances. The table records current local claim holders; unclaimed means
no claim file was present. Only the item module is edited.

Repair of the return for head `7e062ee8ca`: the landing-side check identified three
additional consumers, listed first below. They are absent from this machine's current
read-only source snapshot, so these rows retain the landing check's consumer evidence
rather than treating their absence here as withdrawal. No local claim exists for them.
Their referenced declarations retain their exported types and mathematical data:
`completionUnit` merely expands its original choice application, `reduction` and `hom`
only gain their previously inferred types, and `generator_original_formula` proves the
generator's original formula by reflexivity. These consumers need no adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralCompletionUnitCriterion | unclaimed locally; landing-side consumer | uses `completionUnit`; identical choice application and exported type; no adaptation |
| Sheaf.Paper.IntegralFiniteTensorComparison | unclaimed locally; landing-side consumer | uses `reduction`, `generator`, `hom`; identical exported types and generator formula; no adaptation |
| Sheaf.Paper.IntegralLineRoosTensor | unclaimed locally; landing-side consumer | uses `hom`; identical exported type and body; no adaptation |
| Sheaf.Paper.IntegralDerivedOperationsOnSlices | V9 | two theorem proofs completed; proved object equation and proof interfaces added |
| Sheaf.Algebra.Homology.DerivedTensorTruncationWindow | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.FiniteConstantLocalModel | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.FrobeniusFactorization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.GenericFiberComponentsSection | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.SfEtaleExchanges | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.SheafExtCoherent | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicHeartPullbackFibres | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicPullbackPresentationTransport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicPurityObjects | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicSmoothBaseChange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AffineLineInvariance | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AmbientCompleteCoefficientCategories | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AmbientCompleteRawSystem | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ArithmeticRoots | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.BoundaryQMaps | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.BoundaryQTransport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.BoundedConstructibleBaseChange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CartesianCoefficients | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | E2 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientExtensionReductionModel | Z9 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientFiniteDescentHom | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientFiniteDescentSections | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientHeart | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientHeartTriangulated | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoefficientTwistsDetailed | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoherentRationalPullbackIdentity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CommonStageCalculus | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CommonStageLisse | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CommonStageLocallyFree | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CommonStagePullbackIdentity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactSupportReductionTower | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompleteProetale | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompletedCoefficientPresentationTransport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompletedCompactSupportExchange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompletedExchangeCoherence | S9 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompletedMapReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompletedOpenExchangeTransport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompletedOperationTowerSubstitution | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompletedPullbackReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompletedPullbackTensorComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompletedReductionSquare | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompletedScalarShift | F3 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CompletedTensorScalarLinearity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedCompactSupportProjection | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedERealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedPointCoefficients | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedPointDiscreteConstantComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CondensedTateRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstantToContinuousScalarFlat | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstantWeilStructure | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstructibleFlatCohomologyTorBound | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstructiblePullbackTExact | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ConstructibleTruncations | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CurveMiddleExtension | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DerivedCompleteOnSlices | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DerivedNakayama | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DerivedNakayamaFirstReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DerivedNakayamaResolution | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DerivedPullbackTensorHom | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DerivedPullbackTensorIso | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ECoefficientSmoothBaseChange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.EtaleIntegralLineDerivedComplete | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.EtaleIsoDescent | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ExplicitExceptionalPreservation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FdCoefficientComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FdPullbackComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FieldTwistInverse | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FilteredCoefficientTensorBounds | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteCoefficientPoint | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteConstantModelResolution | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteExtensionReductionConeBound | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteFreeCompletedScalarComparison | V8 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteModelStratumFiltration | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteProjectionActionLaws | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteProperBaseChange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FinitePullbackTensorComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteTateSiteDescent | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteTorStability | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteWindow | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FormalClosedSupport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FormalClosedSupportDerived | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FormalClosedSupportSheaves | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FourierAdicArtinSchreier | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FourierTraceFormula | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.GeometricStalkPerfect | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.HomFiniteProjective | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IdentificationFibreAdjunction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralCanonicalTruncations | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralCoefficientExtComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralCoherenceTower | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralComparisonSequenceSystems | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralCriterionReductions | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralCtfTriangulated | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralDerivedCoefficientData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralDirectImageTower | M2 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralExtensionByZero | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralHeartLocalDualityDescent | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralHeartLocalModel | C2 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralHomReduction | M4 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralLineTensorComparison | H7 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralLineTensorCompleteness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralModels | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralOpenExtensionReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralOperationsPreserveConstructible | T5 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralOperationsScalarComparisons | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralProperReductionBound | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralProperReductionModel | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralPullbackComparisonRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralPullbackCompletedComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralPullbackComposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralPullbackReductionCounit | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralPullbackResolutionMatching | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralPullbackSystemComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralStratifiedPerfectCharacterization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralSystemPullbackLiftAssociativity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralSystemReductionFullyFaithful | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralTStructure | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralTensorShriek | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralTowerInverseImageUnit | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralTowerLimitComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.InternalHomDualTorAmplitude | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.InternalHomPullback | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntrinsicCoefficientTwists | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IntrinsicQbarCategory | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.InverseImagePullbackComparisonDerived | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IsomorphismDerivedPullback | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.IteratedWeilMap | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.KummerAdditivity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.LocalFrobeniusTrace | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.LocalizedTStructure | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.LocalizedTensorBraidingNaturality | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.LocallyConstantPerfectComplex | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.MateOpenRestriction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.MixedReductionUnit | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.MixedWeightsStability | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.NormalizedDVREffectivity | T6 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.OpenFiltrationSuccessor | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PadicIntegersInvertEll | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcCohomologySheaves | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcCommonStageCones | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcConeIndependence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcConstructibleReductionPullback | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcDescentFunctors | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcDistinguishedDiagramLifting | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcFiniteRawScalarComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcFiniteStageKaroubian | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcIdempotentCompleteTriangulation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcIntrinsicTowerComplete | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcQbarCategory | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcQbarCompletedPullback | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcQbarIdempotentComplete | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcQbarStandardCohomology | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcScalarExtension | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcSupportCondition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PbcVerdierAxioms | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointDerivedHomEvaluation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointFibreDerivedTensor | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointFibreDerivedTensorBasic | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointFibreDerivedTensorFiniteModels | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointFibreDerivedTensorModels | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointFibreDerivedTensorQbar | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointFibreDerivedTensorRational | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointFibreDerivedTensorScalar | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointFibreEquivalence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointReductionUnitNormalization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointReductionUnits | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointSectionsDerivedReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointSectionsFiniteReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointSectionsFiniteness | P3 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointSectionsReconstruction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointSectionsScalarExtension | G2 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PointSectionsTensorShift | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProjectionSectionNormalization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperHeartBound | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperHeartBoundTorsion | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperUnboundedWindowBounded | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurAdicScalarExtensionTorBound | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurTwistSheafLocallyFree | W9 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityConventions | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityCoprojection | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityFiniteKummerLevel | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityGysinStructure | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PuritySourceTransports | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.QbarIdempotentComplete | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RationalCoefficientCategoryComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RationalSliceCompletedEvaluation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RationalStalkExact | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RationalThickEvaluation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RealSheafSections | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ResidueLisseProjectiveModels | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.RestrictionLocal | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SbcCompletedOperations | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ScalarExtensionExactIntrinsic | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ScalarExtensionTensorUnit | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ScalarExtensionTowerCoherence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SectionDerivedRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SectionModuleOperationsData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfAlgebraicallyClosedCoefficients | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfBidualityClass | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfConstructibleHeart | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfExchanges | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfImmersionCompletedPullbackComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfIntegralConstructibleLinear | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfIntegralConstructibleTriangulated | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfIntegralDirectImageConstructible | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfIntegralStandardTruncations | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfRationalBoundedConeTorsion | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfRationalLocalGlobalPowerTorsion | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfRationalizationKaroubi | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfScalarExtensionComposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SfWeilSheafComplex | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SignedLineTensorEquivalence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SignedTwistReductionComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SitePerfectComplex | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SixFunctorDatum | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SmoothPurityMap | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SmoothTrace | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.StratifiedLattice | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SupportedHomPullback | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TAdmissibleCoefficientModels | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TowerClassChern | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TowerClassFinite | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TowerClassProjective | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TowerClassPullback | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TowerClassReduction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TowerClassSystems | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TowerClassTwisting | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TraceFixedScheme | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TwConventions | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.VectorBundlePurity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.VerdierExchange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.WContractibleCondensedScalarEvaluation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.WeilComplexQbarIdempotentComplete | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Paper.ZlShriekComposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SecSmoothPurity.WeilTwistRationalization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.BoundaryDualityInput | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.BrownHypothesesAmbient | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.ClosedImmersionTensorProjection | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.CompletedTensorShiftRight | J8 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.FieldTensor | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.FiniteCoverCTFLocality | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.FrobeniusPointTransport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntTensorProjection | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.IntegralVerdier | V2 | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.OpenImmersionTensorProjection | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.RationalOperations | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.ScalarSixPullback | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.SchemeFrobenius | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.SchemeGaloisComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Targets.PoincareUncurry | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Targets.VectorBundlePurity | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.Topology.ProfiniteCondensedRing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.TraceFormula.PointTransportComposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| TargetsCheck | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.SmoothPurity.Defs | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.TraceFormula.Basic | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.TraceFormula.Statement | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | no adaptation; public signatures, data and attributes unchanged |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | no adaptation; public signatures, data and attributes unchanged |

## Status

landed 20261020T235636-L-1199778 2026-10-20 (merge of deliver/V9/Sheaf.Paper.IntegralDerivedOperationsOnSlices)
