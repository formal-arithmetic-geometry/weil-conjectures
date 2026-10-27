# Integral tensor shift normalization predicates

## Reason

The four tensor-slot existence/uniqueness statements need the existing normalization
predicates without importing their parent theorem. Move the definitions verbatim to
IntegralTensorShiftProperties and publicly reexport them from IntegralOperationShiftData.
This avoids an import cycle. The names, signatures, definition bodies, reducibility,
and meaning of the predicates are unchanged. No target statement or definition meaning changes.

## Old

In lean/Sheaf/SixFunctors/IntegralOperationShiftData.lean:

```lean
/-- Shift only the first operand of a bifunctor.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def tensorShiftFirst (A : Type v) [Category.{w} A] [HasShift A ℤ] (r : ℤ) :
    A × A ⥤ A × A := (shiftFunctor A r).prod (𝟭 A)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual total tensor on complexes of strict systems.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
abbrev systemTotalTensor (W : Scheme.{u}) :=
  coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)

/-- K-flatness on the actual sequence site.
Source: Stacks 06YN (blueprint: def-pur-integral-operation-shift-data). -/
abbrev systemKFlat (W : Scheme.{u})
    (P : CochainComplex (coefficientSequenceModules l E W) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
    (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
    (R := coefficientSequenceCommRingSheaf l E W) P

/-- The unsigned first-slot formula on every strict-system tensor generator.
The tower site includes quotient-linear transitions, so the cochain isomorphism
also fixes all transition squares.
Source: Stacks 011G, 012Z (blueprint: def-pur-integral-operation-shift-data). -/
def systemTensorLeftFormula (W : Scheme.{u})
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ) (r : ℤ)
    (α : (systemTotalTensor l E W).obj (P⟦r⟧, Q) ≅
      ((systemTotalTensor l E W).obj (P, Q))⟦r⟧) : Prop :=
  ∀ (i j : ℤ) (U : (ℕ × W.ProEt)ᵒᵖ)
    (x : (P.X (i + r)).val.obj U) (y : (Q.X (j)).val.obj U),
    ((α.hom.f (i + j)).val.app U)
      (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (P⟦r⟧) (Q) i j (i + j) rfl U x y) =
    ((CochainComplex.shiftFunctorObjXIso ((systemTotalTensor l E W).obj (P, Q))
      r (i + j) ((i + r) + (j)) (by omega)).inv.val.app U)
      (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) P Q (i + r) (j)
          ((i + r) + (j)) rfl U x y)

/-- Descent of the specified cochain shift on every K-flat pair.
Source: Stacks 06YU and blueprint Step 2
(blueprint: def-pur-integral-operation-shift-data). -/
def systemTensorLeftProperty (W : Scheme.{u}) (r : ℤ)
    (σ : tensorShiftFirst (System l E W) r ⋙ (calculus l E W).systemClosed.tensor ≅
      (calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) r) : Prop :=
  ∀ (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : systemKFlat l E W P) (hQ : systemKFlat l E W Q),
    ∃ (hS : systemKFlat l E W (P⟦r⟧))
      (α : (systemTotalTensor l E W).obj (P⟦r⟧, Q) ≅
        ((systemTotalTensor l E W).obj (P, Q))⟦r⟧),
      systemTensorLeftFormula l E W P Q r α ∧
      (calculus l E W).systemClosed.tensor.map
        (X := (DerivedCategory.Q.obj (P⟦r⟧), DerivedCategory.Q.obj Q))
        (Y := ((DerivedCategory.Q.obj P)⟦r⟧, DerivedCategory.Q.obj Q))
        (((DerivedCategory.Q.commShiftIso r).hom.app P), 𝟙 (DerivedCategory.Q.obj Q)) ≫
          σ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      ((calculus l E W).systemTensorModel.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
        (P⟦r⟧) (Q) hS hQ).inv ≫
      DerivedCategory.Q.map α.hom ≫
      (DerivedCategory.Q.commShiftIso r).hom.app ((systemTotalTensor l E W).obj (P, Q)) ≫
      (shiftFunctor (System l E W) r).map
        (((calculus l E W).systemTensorModel.iso
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
          P Q hP hQ).hom)

/-- The signed second-slot formula on every strict-system tensor generator.
The tower site includes quotient-linear transitions, so the cochain isomorphism
also fixes all transition squares.
Source: Stacks 011G, 012Z (blueprint: def-pur-integral-operation-shift-data). -/
def systemTensorRightFormula (W : Scheme.{u})
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ) (r : ℤ)
    (α : (systemTotalTensor l E W).obj (P, Q⟦r⟧) ≅
      ((systemTotalTensor l E W).obj (P, Q))⟦r⟧) : Prop :=
  ∀ (i j : ℤ) (U : (ℕ × W.ProEt)ᵒᵖ)
    (x : (P.X (i)).val.obj U) (y : (Q.X (j + r)).val.obj U),
    ((α.hom.f (i + j)).val.app U)
      (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (P) (Q⟦r⟧) i j (i + j) rfl U x y) =
    ((CochainComplex.shiftFunctorObjXIso ((systemTotalTensor l E W).obj (P, Q))
      r (i + j) ((i) + (j + r)) (by omega)).inv.val.app U)
      ((r * i).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) P Q (i) (j + r)
          ((i) + (j + r)) rfl U x y)

/-- Descent of the specified cochain shift on every K-flat pair.
Source: Stacks 06YU and blueprint Step 2
(blueprint: def-pur-integral-operation-shift-data). -/
def systemTensorRightProperty (W : Scheme.{u}) (r : ℤ)
    (σ : completedTensorShiftSecond (System l E W) r ⋙ (calculus l E W).systemClosed.tensor ≅
      (calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) r) : Prop :=
  ∀ (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : systemKFlat l E W P) (hQ : systemKFlat l E W Q),
    ∃ (hS : systemKFlat l E W (Q⟦r⟧))
      (α : (systemTotalTensor l E W).obj (P, Q⟦r⟧) ≅
        ((systemTotalTensor l E W).obj (P, Q))⟦r⟧),
      systemTensorRightFormula l E W P Q r α ∧
      (calculus l E W).systemClosed.tensor.map
        (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (Q⟦r⟧)))
        (Y := (DerivedCategory.Q.obj P, (DerivedCategory.Q.obj Q)⟦r⟧))
        (𝟙 (DerivedCategory.Q.obj P), ((DerivedCategory.Q.commShiftIso r).hom.app Q)) ≫
          σ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      ((calculus l E W).systemTensorModel.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
        (P) (Q⟦r⟧) hP hS).inv ≫
      DerivedCategory.Q.map α.hom ≫
      (DerivedCategory.Q.commShiftIso r).hom.app ((systemTotalTensor l E W).obj (P, Q)) ≫
      (shiftFunctor (System l E W) r).map
        (((calculus l E W).systemTensorModel.iso
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
          P Q hP hQ).hom)

/-- The first-slot finite tensor formula, before the fixed product/cone passage.
Source: Stacks 011G (blueprint: def-pur-integral-operation-shift-data). -/
def integralTensorLeftFormula (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ)
    (α : (integralOperationsTensorTowerFunctor l E W).obj (P⟦r⟧, Q) ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P, Q) ⋙
        shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r) : Prop :=
  ∀ (n : ℕ) (i j : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X (i + r)).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X j).val.obj U),
    (((α.hom.app (op n)).f (i + j)).val.app U)
      (integralOperationsTotalTensorSection l E W n (P⟦r⟧) Q i j U x y) =
    ((CochainComplex.shiftFunctorObjXIso
      ((integralOperationsTensorLevel l E W n).obj (P, Q))
        r (i + j) ((i + r) + j) (by omega)).inv.val.app U)
      (integralOperationsTotalTensorSection l E W n P Q (i + r) j U x y)

/-- First-slot descent through exactly the recorded finite tower and Roos cone.
Source: Stacks 014E, 0941 (blueprint: def-pur-integral-operation-shift-data). -/
def integralTensorLeftProperty (W : Scheme.{u}) (r : ℤ)
    (σ : tensorShiftFirst (Integral l E W) r ⋙ integralCompletedTensor l E W ≅
      integralCompletedTensor l E W ⋙ shiftFunctor (Integral l E W) r) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory),
    ∃ (hP : integralOperationsGoodComplex l E W (P.obj⟦r⟧))
      (α : (integralOperationsTensorTowerFunctor l E W).obj (P.obj⟦r⟧, Q.obj) ≅
        (integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj) ⋙
          shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r),
      integralTensorLeftFormula l E W P.obj Q.obj r α ∧
      ∃ (δ : CochainComplex.mappingCone (completedTensorShiftOneSub
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj⟦r⟧, Q.obj))) ≅
          (CochainComplex.mappingCone (completedTensorShiftOneSub
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))))⟦r⟧),
        completedTensorShiftConeFormula
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj⟦r⟧, Q.obj)) r α δ ∧
        (integralCompletedTensor l E W).map
            (((DerivedCategory.Q.commShiftIso r).hom.app P.obj),
              𝟙 (DerivedCategory.Q.obj Q.obj)) ≫
          σ.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (shiftFunctor (Integral l E W) r).map
            ((integralCompletedTensorComparison l E W).hom.app (P, Q)) =
        (integralCompletedTensorComparison l E W).hom.app (⟨P.obj⟦r⟧, hP⟩, Q) ≫
          DerivedCategory.Q.map
            (completedTensorShiftRoosIso
              ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
              ((integralOperationsTensorTowerFunctor l E W).obj (P.obj⟦r⟧, Q.obj)) r δ).hom ≫
          (DerivedCategory.Q.commShiftIso r).hom.app
            ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj))
```

## New

The exact same declarations, including the variable context above, now occur in
lean/Sheaf/SixFunctors/IntegralTensorShiftProperties.lean. The parent adds:

```lean
public import Sheaf.SixFunctors.IntegralTensorShiftProperties
```

All six existing public imports of the parent are retained. Only the proof of
`tensorShifts_existsUnique` changes beyond this relocation. No consumer needs adaptation:
the old module publicly reexports every moved declaration, with its original body.
The new property module needs only IntegralSystemExpressionDomain and CompletedTensorShiftRight;
its import list omits the unrelated occurrence, pullback-shift, Roos-model and adjunction APIs.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | P3 | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicTraceTransposeData | H1 | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.TwistedPullbackSquareScalars | S2 | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | W4 | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | A5 | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | J6 | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same reexported names, signatures and bodies; no edit needed. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Same reexported names, signatures and bodies; no edit needed. |

## Status

landed 20261025T161932-L-154737 2026-10-25 (merge of deliver/A9/Sheaf.SixFunctors.IntegralOperationShiftData)
