# WeilConjectures.LocallyFiniteAdicCompactSupport.native_integral_scalar_morphism_normalization

## Reason

The disputed theorem inferred the prescribed six canonical arrows from a factorization
through arbitrary outer isomorphisms. Negating tau and its left outer isomorphism
preserves that hypothesis, while the prescribed formula keeps its sign. The direct
construction fixes the outer comparisons before composing the scalar mate.

The replacement accepts an arbitrary scalar natural transformation with the indicated
coefficient-map endpoints, and constructs a native natural transformation together with
its factorization and six-arrow formula. This construction specializes to the
original proper/open mate in the sole parent. The parent's full statement, including
`IntegralComponent`, remains unchanged. No target or source-library signature, data,
attribute or public import is changed. No existing coefficient or geometric definition
is changed.

The two new supporting modules prove the finite-stage comparison and the natural
boundary isomorphisms with their component formulas. The item composes those
boundaries with the supplied scalar mate and lifts the composite; no intermediate
obligation is left unfinished. They separate the concrete boundary constructions
from the scalar lift after profiling the coefficient-category conversions.

The proof restricts unfolding locally around the stage and coefficient categories;
all such attributes are local. It uses neither new unproved statements nor an arbitrary
witness selected from an unproved existence theorem. The only preimage used is the
unique lift through a fully faithful derived section functor.

## Old

```lean
theorem native_integral_scalar_morphism_normalization [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (stage : StageAction l D hl P c)
    (change : ∀ E : Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (hs : ∀ E, (change E).map X = (source.coefficient E).integralMap l X)
    (ht : ∀ E, (change E).map Y = (target.coefficient E).integralMap l Y)
    (E : Index l (PadicAlgCl l))
    (tau : sfRationalConstructibleLocalization l
        (Coefficient l (PadicAlgCl l) E) X ⋙
        finiteSourceAux l D hl P c target stage E ⟶
      sfRationalConstructibleLocalization l
        (Coefficient l (PadicAlgCl l) E) X ⋙
        finiteTargetAux l c source E)
    (hfac : ∀ K : finiteTorConstructibleIntegralCategory l
        (Coefficient l (PadicAlgCl l) E) X,
      ∃ (b : (sections l Y).mapDerivedCategory.obj
            ((sfRationalConstructibleLocalization l
              (Coefficient l (PadicAlgCl l) E) X ⋙
              finiteSourceAux l D hl P c target stage E).obj
                ((PurCompactSupport.finiteTorIntegralInclusion l
                  (Coefficient l (PadicAlgCl l) E) X).obj K)) ≅
          (PurCompactSupport.image (PurCompactSupport.completed l
            (Coefficient l (PadicAlgCl l) E)) c ⋙
            pbcDerivedExtend ((change E).map Y)).obj K.obj)
        (d : (pbcDerivedExtend ((change E).map X) ⋙
            PurCompactSupport.image (nativeCoefficients l) c).obj K.obj ≅
          (sections l Y).mapDerivedCategory.obj
            ((sfRationalConstructibleLocalization l
              (Coefficient l (PadicAlgCl l) E) X ⋙
              finiteTargetAux l c source E).obj
                ((PurCompactSupport.finiteTorIntegralInclusion l
                  (Coefficient l (PadicAlgCl l) E) X).obj K))),
        (sections l Y).mapDerivedCategory.map
            (tau.app ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient l (PadicAlgCl l) E) X).obj K)) =
          b.hom ≫ (PurCompactSupport.comparison (change E) c).app K.obj ≫ d.hom)
    (K : finiteTorConstructibleIntegralCategory l
      (Coefficient l (PadicAlgCl l) E) X) :
    let rationalInput :=
      (rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K
    let input := (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj rationalInput
    ∃ (A B : sfRationalConstructibleCategory l
          (Coefficient l (PadicAlgCl l) E) Y) (r : A ⟶ B),
      HEq r ((P.ring.rationalLeft c (finiteField l E)).hom.app rationalInput) ∧
    ∃ (M₁ M₂ M₃ M₄ M₅ : DerivedCategory
          (proEtaleRingModules Y (ringSheaf l Y)))
      (a₀ : (sections l Y).mapDerivedCategory.obj
        ((sfRationalConstructibleLocalization l
          (Coefficient l (PadicAlgCl l) E) X ⋙
          finiteSourceAux l D hl P c target stage E).obj
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient l (PadicAlgCl l) E) X).obj K)) ⟶ M₁)
      (a₁ : M₁ ⟶ M₂) (a₂ : M₂ ⟶ M₃) (a₃ : M₃ ⟶ M₄) (a₄ : M₄ ⟶ M₅)
      (a₅ : M₅ ⟶ (sections l Y).mapDerivedCategory.obj
        ((sfRationalConstructibleLocalization l
          (Coefficient l (PadicAlgCl l) E) X ⋙
          finiteTargetAux l c source E).obj
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient l (PadicAlgCl l) E) X).obj K))),
      HEq a₀ ((sections l Y).mapDerivedCategory.map
        (target.J.map ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := Y) E).map r))) ∧
      HEq a₁ ((target.integral E).hom.app
          ((sfCompactSupportFiniteIntegralFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c
            (Coefficient l (PadicAlgCl l) E)).obj
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₂ ((pbcDerivedExtend ((target.coefficient E).integralMap l Y)).map
          ((sfQcqsCompactSupportRealization l (Coefficient l (PadicAlgCl l) E)
            D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₃ ((PurCompactSupport.comparison (change E) c).app K.obj) ∧
      HEq a₄ ((PurCompactSupport.image (nativeCoefficients l) c).map
          ((source.integral E).inv.app
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₅ ((operationTransport l c).inv.app (source.J.obj input)) ∧
      (sections l Y).mapDerivedCategory.map
          (tau.app ((PurCompactSupport.finiteTorIntegralInclusion l
            (Coefficient l (PadicAlgCl l) E) X).obj K)) =
        a₀ ≫ a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅
```

## New

```lean
theorem native_integral_scalar_morphism_normalization [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (stage : StageAction l D hl P c) (E : Index l (PadicAlgCl l))
    (sx : (PurCompactSupport.completed l (Coefficient l (PadicAlgCl l) E)).ring X ⟶
      (nativeCoefficients l).ring X)
    (sy : (PurCompactSupport.completed l (Coefficient l (PadicAlgCl l) E)).ring Y ⟶
      (nativeCoefficients l).ring Y)
    (hs : sx = (source.coefficient E).integralMap l X)
    (ht : sy = (target.coefficient E).integralMap l Y)
    (beta : PurCompactSupport.image (PurCompactSupport.completed l
        (Coefficient l (PadicAlgCl l) E)) c ⋙ pbcDerivedExtend sy ⟶
      pbcDerivedExtend sx ⋙ PurCompactSupport.image (nativeCoefficients l) c) :
    ∃ tau : sfRationalConstructibleLocalization l
        (Coefficient l (PadicAlgCl l) E) X ⋙
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ stage.system.functor ⋙ target.J) ⟶
      sfRationalConstructibleLocalization l
        (Coefficient l (PadicAlgCl l) E) X ⋙
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J ⋙ actual l c),
      ∀ K : finiteTorConstructibleIntegralCategory l
          (Coefficient l (PadicAlgCl l) E) X,
        (∃ (b : (sections l Y).mapDerivedCategory.obj
              ((sfRationalConstructibleLocalization l
                (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
                (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ stage.system.functor ⋙ target.J)).obj
                  ((PurCompactSupport.finiteTorIntegralInclusion l
                    (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)) ≅
            (PurCompactSupport.image (PurCompactSupport.completed l
              (Coefficient.{u} l (PadicAlgCl l) E)) c ⋙
              pbcDerivedExtend sy).obj K.obj)
          (d : (pbcDerivedExtend sx ⋙
              PurCompactSupport.image (nativeCoefficients l) c).obj K.obj ≅
            (sections l Y).mapDerivedCategory.obj
              ((sfRationalConstructibleLocalization l
                (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
                (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J ⋙ actual l c)).obj
                  ((PurCompactSupport.finiteTorIntegralInclusion l
                    (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))),
          (sections l Y).mapDerivedCategory.map
              (tau.app ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)) =
            b.hom ≫ beta.app K.obj ≫ d.hom) ∧
    let rationalInput :=
      (rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K
    let input := (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj rationalInput
    ∃ (A B : sfRationalConstructibleCategory l
          (Coefficient l (PadicAlgCl l) E) Y) (r : A ⟶ B),
      HEq r ((P.ring.rationalLeft c (finiteField l E)).hom.app rationalInput) ∧
    ∃ (M₁ M₂ M₃ M₄ M₅ : DerivedCategory
          (proEtaleRingModules Y (ringSheaf l Y)))
      (a₀ : (sections l Y).mapDerivedCategory.obj
        ((sfRationalConstructibleLocalization l
          (Coefficient l (PadicAlgCl l) E) X ⋙
          (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ stage.system.functor ⋙ target.J)).obj
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient l (PadicAlgCl l) E) X).obj K)) ⟶ M₁)
      (a₁ : M₁ ⟶ M₂) (a₂ : M₂ ⟶ M₃) (a₃ : M₃ ⟶ M₄) (a₄ : M₄ ⟶ M₅)
      (a₅ : M₅ ⟶ (sections l Y).mapDerivedCategory.obj
        ((sfRationalConstructibleLocalization l
          (Coefficient l (PadicAlgCl l) E) X ⋙
          (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J ⋙ actual l c)).obj
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient l (PadicAlgCl l) E) X).obj K))),
      HEq a₀ ((sections l Y).mapDerivedCategory.map
        (target.J.map ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := Y) E).map r))) ∧
      HEq a₁ ((target.integral E).hom.app
          ((sfCompactSupportFiniteIntegralFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c
            (Coefficient l (PadicAlgCl l) E)).obj
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₂ ((pbcDerivedExtend ((target.coefficient E).integralMap l Y)).map
          ((sfQcqsCompactSupportRealization l (Coefficient l (PadicAlgCl l) E)
            D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₃ (beta.app K.obj) ∧
      HEq a₄ ((PurCompactSupport.image (nativeCoefficients l) c).map
          ((source.integral E).inv.app
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₅ ((operationTransport l c).inv.app (source.J.obj input)) ∧
      (sections l Y).mapDerivedCategory.map
          (tau.app ((PurCompactSupport.finiteTorIntegralInclusion l
            (Coefficient l (PadicAlgCl l) E) X).obj K)) =
        a₀ ≫ a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅
```

The import of the weaker existence module is replaced by the underlying compact-support
data module. The finite-stage source and target expressions are written directly; no
new definition of these functors is introduced. The only adapted existing module is
`Sheaf.Paper.NativeCompactSupportIntegralScalarMorphism`, unclaimed on the current server
when checked at the start of this task. Its final proof obtains the constructed tau and
pairs the two component properties. All its declaration signatures, bodies of definitions,
attributes and imports remain verbatim.

## Users

Only the direct parent mentions the changed theorem. The following table also lists
all transitive importers reported by `tools/downstream.py --uses`; holder entries for
unedited modules are read from the shared snapshot. The changed theorem is a private
proof import of the parent, whose public interface is preserved. No further caller
requires adaptation. Related-module compilation is performed by `deliver3.py`.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.DeligneLaumon.MarkedGeometricCurveModel | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.AdicNormalizedPullbackRealization | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.AdicProperOrdinaryPushPreservation | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.ArithmeticRoots | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.CompactSupportStageActionAdjunction | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.DerivedWeilOperations | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeAdicCompactSupportSums | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeCompactSupportFiniteComparison | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeCompactSupportFiniteScalarCoherence | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeCompactSupportFiniteScalarCoherenceGenerator | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeCompactSupportIntegralLocalization | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeCompactSupportIntegralScalarMorphism | unclaimed on server | Proof updated to use the constructor; every signature and definition unchanged. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeProperProjectionComparisons | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeProperProjectionRealization | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeWeilComparisonStructure | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeWeilDerivedInductionComparison | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeWeilDualizingHomTransposition | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeWeilFreeCoproduct | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeWeilHeartProperties | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeWeilInductionComparisonData | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeWeilInductionSummands | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeWeilProperNormalization | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.CompactSupportBrownConstructibility | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.NativeExceptionalCounitHomSquares | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.NativeExceptionalHomTransport | S1 | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.NativeExceptionalLeftModels | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounit | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitComparison | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitWitness | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.StructuralBidualInvertible | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.StructuralDualizingIdentification | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| TargetsCheck | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.Statement | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.Curve | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.Karoubian | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.KaroubianPointer | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.ZetaFunction.Examples | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| WeilConjectures.ZetaFunction.Weights | unclaimed in shared snapshot | Unedited; parent interface unchanged, and this module does not mention the corrected declaration. |
| Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismNormalization | M4 | Corrected constructor, proved directly; own item. |

## Status

landed 20261028T020605-L-2527308 2026-10-28 (merge of deliver/M4/Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismNormalization)
