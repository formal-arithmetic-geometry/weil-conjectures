# AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible

## Reason

Remove the restored noetherian-only instance, which is false for arbitrary coefficient
rings. The existing conditional instance
`AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible_of_serre` remains unchanged,
including its name, priority, hypotheses and proof. No definition or target statement changes.
This is retirement of a false assertion, not a proof of it and not a weaker replacement.

The obstruction already occurs over a geometric point with discrete coefficients. Let
`k` be a field and let `V` be an infinite-dimensional `k`-vector space. Give
`B = k ⊕ V` square-zero multiplication `(a,v)(b,w) = (ab, aw+bv)`.
For nonzero `e ∈ V`, multiplication by `(0,e)` on `B` has kernel `0 ⊕ V`:
its value at `(a,v)` is `(0,ae)`, which vanishes exactly when `a=0`.
The `B`-action on this kernel factors through `k`, so any finite set generates only a
finite-dimensional subspace. The kernel is not finitely generated, hence not finitely
presented. Its source and target are free of rank one. Constant discrete sheaves on the
pro-etale site of a separably closed point give the same example: a local finite
presentation would remain a finite presentation on the geometric fiber. There is only
one nonempty stratum. The cone of the map of the two degree-zero free-module complexes
has this kernel as a cohomology sheaf, so it is not constructible. Both endpoints are
bounded constructible and the base is topologically noetherian. This contradicts the
retired assertion. The zero ring and finite-dimensional `V` cases do not create this
obstruction; the displayed example explicitly uses nonzero `e` and infinite-dimensional `V`.

The same counterexample and correction were documented in
coord/changes/proetale-module-constructible-triangulated.md. The current base restored
the false instance beside the proved conditional instance. This delivery removes that false duplicate and corrects the module-docstring link.
It also publishes the unconditional zero, isomorphism and integer-shift closure already
implicit in the existing proof, so users do not need triangulated closure for these facts.

Compiling the direct importers exposed the necessary adaptation of the unclaimed module
`WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`: its rationalization
signatures require `Pretriangulated` on the integral bounded constructible category.
The original file fails at its original lines 155, 163, 167 and 173 after retirement of the
false instance, with failed synthesis of HasZeroObject/HasShift and then Pretriangulated.
The public import of `Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated` supplies
the correct coefficient-specific instance. That new module specializes the existing
`CondensedRing.integralConstructible_serre` to the induced norm on a finite p-adic
subfield and applies the retained conditional instance. All its proof is complete;
no new obligation or additional assumption is introduced. EllAdicRationalization's
existing signatures, visibility, definitions and proof terms stay textually identical;
only the import and the now-accurate triangulation explanation in its docstring change.

## Old

```lean
/-- The bounded constructible complexes on a topologically noetherian scheme form a triangulated
subcategory. -/
instance isTriangulated_boundedConstructible [TopologicalSpace.NoetherianSpace X] :
    (boundedConstructible R).IsTriangulated :=
  sorry
```

## New

The false declaration is removed. The following existing declaration and its complete
proof remain unchanged:

```lean
instance (priority := 2000) isTriangulated_boundedConstructible_of_serre
    [ObjectProperty.IsClosedUnderKernels (IsConstructibleModuleObject R)]
    [ObjectProperty.IsClosedUnderCokernels (IsConstructibleModuleObject R)]
    [ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject R)] :
    (boundedConstructible R).IsTriangulated := by
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsConstructibleModuleObject R) :=
    ⟨fun e hM ↦ constructible_of_iso R e hM⟩
  have : ObjectProperty.ContainsZero (IsConstructibleModuleObject R) :=
    ⟨0, isZero_zero _, constructible_of_isZero R (isZero_zero _)⟩
  change (DerivedCategory.TStructure.t.bounded ⊓
    DerivedCategory.homologyProperty (IsConstructibleModuleObject R)).IsTriangulated
  infer_instance
```

The following unconditional API is added to the item module:

```lean
/-- Bounded constructibility is invariant under isomorphisms.

Source: `DerivedCategory.homologyProperty` and Mathlib's canonical bounded t-structure.
Proof: transport each cohomology presentation across the homology of the isomorphism;
boundedness is invariant under isomorphisms as well.
(blueprint: prop-weil-pbc-module-bounded-constructible-triangulated) -/
instance isClosedUnderIsomorphisms_boundedConstructible :
    (boundedConstructible R).IsClosedUnderIsomorphisms := by
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsConstructibleModuleObject R) :=
    ⟨fun e hM ↦ constructible_of_iso R e hM⟩
  change (DerivedCategory.TStructure.t.bounded ⊓
    DerivedCategory.homologyProperty (IsConstructibleModuleObject R)).IsClosedUnderIsomorphisms
  infer_instance

/-- The zero complex is bounded constructible for any coefficient ring.

Source: `DerivedCategory.homologyProperty` and Mathlib's canonical bounded t-structure.
Proof: all homology objects of zero are zero; the zero module is constructible by the
rank-zero presentation and the single-stratum stratification. Zero is bounded.
(blueprint: prop-weil-pbc-module-bounded-constructible-triangulated) -/
instance containsZero_boundedConstructible : (boundedConstructible R).ContainsZero := by
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsConstructibleModuleObject R) :=
    ⟨fun e hM ↦ constructible_of_iso R e hM⟩
  have : ObjectProperty.ContainsZero (IsConstructibleModuleObject R) :=
    ⟨0, isZero_zero _, constructible_of_isZero R (isZero_zero _)⟩
  change (DerivedCategory.TStructure.t.bounded ⊓
    DerivedCategory.homologyProperty (IsConstructibleModuleObject R)).ContainsZero
  infer_instance

/-- Every integer shift of a bounded constructible complex is bounded constructible.

Source: `DerivedCategory.homologyProperty` and Mathlib's canonical bounded t-structure.
Proof: homology of a shift is isomorphic to homology in the translated degree. Transport
constructibility across this isomorphism; translation preserves boundedness.
(blueprint: prop-weil-pbc-module-bounded-constructible-triangulated) -/
instance isStableUnderShift_boundedConstructible :
    (boundedConstructible R).IsStableUnderShift ℤ := by
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsConstructibleModuleObject R) :=
    ⟨fun e hM ↦ constructible_of_iso R e hM⟩
  change (DerivedCategory.TStructure.t.bounded ⊓
    DerivedCategory.homologyProperty (IsConstructibleModuleObject R)).IsStableUnderShift ℤ
  infer_instance

```

The adapted module gains this public import:

```lean
public import Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated
```

The new module's complete coefficient-specific instance is:

```lean
instance isTriangulated_boundedConstructible_padicIntegers :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)).IsTriangulated := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  obtain ⟨hker, hcok, hext⟩ := CondensedRing.integralConstructible_serre ℓ E.1 X
  change ObjectProperty.IsClosedUnderKernels
    (IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) at hker
  change ObjectProperty.IsClosedUnderCokernels
    (IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) at hcok
  change ObjectProperty.IsClosedUnderExtensions
    (IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) at hext
  exact isTriangulated_boundedConstructible_of_serre _

```

## Users

Validation: the repaired item compiles in 3.8 seconds, the new integral coefficient
instance in 4.8 seconds, and the adapted rationalization module in 26.9 seconds without
warnings. Eight direct importers compile against the repaired module. Two checks have
independent baseline import failures: Derived.BoundedConstructible cannot find
WeilConjectures.Mathlib.CategoryTheory.Monoidal.Subcategory.olean (the same failure was
reproduced without the sandbox overlay), and the umbrella WeilConjectures cannot find
WeilConjectures.Algebra.Category.ModuleCat.Presheaf.TopologicalPullback.olean. Those
sources are not changed to work around missing published artifacts. The bounded
six-functor source contains no use of triangulated closure; its operations are restrictions
of ambient functors to the unchanged full subcategories.

`tools/downstream.py` lists 233 transitive downstream modules; its `--uses`
scan finds the removed name only in the item itself. The retained conditional name has
one explicit consumer, `Sheaf.Paper.CondensedFiniteModelProofAPI`, which supplies its
closure hypotheses. Every downstream module is listed below with its current holder.
No existing definition (including boundedConstructible, BoundedConstructible and the
constructible-module predicate), public import, or target signature is changed.
The target statements do not use the retired instance; their meanings are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory | C4 | Retire the false generic assertion; prove unconditional zero/isomorphism/shift closure. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexPresentation | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | B2 | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedCoefficientFamilyHomStage | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedCoefficientHomStage | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedConstructiblePiece | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | C1 | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedFinitePresentationMatrices | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedFpHomStage | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedLocallyClosedPiece | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedQbarPullbackCube | E1 | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedQbarScalarPullback | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralCoefficientTelescope | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralCoefficients | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralDerivedUnit | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralScalarExact | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousLocallyFreePullback | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | E4 | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | F1 | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | B3 | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | F2 | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralReductionScalar | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralReductionTensor | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralReductionTriangulatedProperty | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResidueComparisonInterface | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResidueComparisons | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResidueDerivedMonoidal | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResidueOrdinaryMonoidal | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResidueOrdinaryRestrictPullComp | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResiduePerfect | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResidueProjectionNormalization | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResiduePullFlatModel | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResiduePullOrdinaryUnit | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResiduePullSquare | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResiduePullSquareComp | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResiduePullSquareData | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResiduePullSquareIsIso | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResiduePullbackPreservesFlat | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResidueRestrictPullComp | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResidueScalarGeometryBridge | A2 | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResidueScalarRouteModel | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResidueTensorGeometry | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResidueTensorModel | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResidueTensorPresentation | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResidueTensorPullPresentation | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResidueTensorRouteModel | B4 | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralResidueTensorSquare | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| TargetsCheck | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Add the integral coefficient triangulation import; preserve existing signatures, definitions, proof terms and visibility. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | A4 | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | G2 | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.SmoothPurity.Defs | G1 | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.TraceFormula.Frobenius | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.TraceFormula.Main | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.TraceFormula.Stalk | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | No textual use of the removed declaration; category definitions and signatures unchanged. |
| Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated | C4 (new) | New proved integral coefficient triangulation instance from existing Serre closure. |

## Status

landed 20261016T221601-L-1612345 2026-10-16 (merge of deliver/C4/WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory)
