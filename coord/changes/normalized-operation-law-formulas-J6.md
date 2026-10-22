# OperationTensorLaws and OperationModelLaws

## Reason

Kernel checking the large law structures repeatedly expanded the pure-section, cochain and quotient field propositions. A compact declaration-only profile took 39.7 seconds, with 46.1 cumulative seconds in kernel checks; naming those same three formulas reduced it to 9.6 seconds and 7.74 cumulative seconds. The complete module remains one file. Each new definition is exactly the old field proposition, with no new hypothesis or conclusion and no hole. The three structure fields refer to these named propositions. All other fields and the main theorem signature stay unchanged. Any target that uses these structures has the identical meaning, by definitional equality; this record makes that definition review explicit.

## Old

```lean
structure OperationTensorLaws (A : Data.{c, v, r} J B τ) : Prop where
  /-- Tensor preserves normalization. -/
  normalized : ∀ (M N : DS.{c, v, max c v r} J B τ),
    Normalized.{c, v, max c v r} J B τ A.scalar M → Normalized.{c, v, max c v r} J B τ A.scalar N →
      Normalized.{c, v, max c v r} J B τ A.scalar (A.closed.tensor.obj (M, N))
  /-- The adjoint of the actual tensor transition is monoidal scalar extension
  followed by the tensor of the two original adjoints. -/
  transition : ∀ (M N : DS.{c, v, max c v r} J B τ) {m n : ℕ} (h : n ≤ m),
    reduction.{c, v, max c v r} J B τ h (A.scalar h) (A.closed.tensor.obj (M, N)) ≫
        (A.tensorEvaluation n).hom.app (M, N) =
      (A.scalar h).T.map ((A.tensorEvaluation m).hom.app (M, N)) ≫
        (A.scalarTensor h).hom.app ((e.{c, v, max c v r} J B τ m).obj M, (e.{c, v, max c v r} J B
          τ m).obj N) ≫
        (A.levelClosed n).tensor.map
          (Prod.mkHom (reduction.{c, v, max c v r} J B τ h (A.scalar h) M)
            (reduction.{c, v, max c v r} J B τ h (A.scalar h) N))
  /-- The actual input transition factors through its scalar-insertion unit. -/
  input_factor : ∀ (M : DS.{c, v, max c v r} J B τ) {m n : ℕ} (h : n ≤ m),
    (derivedTransition.{c, v, max c v r} J B τ h).app M =
      (A.scalar h).adjunction.unit.app ((e.{c, v, max c v r} J B τ m).obj M) ≫
        (resD.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)).map (reduction.{c, v,
          max c v r} J B τ h (A.scalar h) M)
  /-- Successive output adjoints equal the direct output adjoint. -/
  cocycle : ∀ (M N : DS.{c, v, max c v r} J B τ)
    {k m n : ℕ} (h : n ≤ m) (j : m ≤ k),
    (A.scalar h).T.map
        (reduction.{c, v, max c v r} J B τ j (A.scalar j) (A.closed.tensor.obj (M, N))) ≫
        reduction.{c, v, max c v r} J B τ h (A.scalar h) (A.closed.tensor.obj (M, N)) =
      (A.scalarComposition h j).hom.app
          ((e.{c, v, max c v r} J B τ k).obj (A.closed.tensor.obj (M, N))) ≫
        reduction.{c, v, max c v r} J B τ (h.trans j) (A.scalar (h.trans j)) (A.closed.tensor.obj
          (M, N))
  /-- On local flat representatives the scalar adjoint uses the actual transitions,
  sending (a tensor x) tensor b to tau(a) tensor b tau(x). -/
  pure : ∀ (M N : Systems.{c, v, max c v r} J B τ)
    (_hM : flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ)
      ((CochainComplex.singleFunctor (Systems.{c, v, max c v r} J B τ) 0).obj M))
    (_hN : flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ)
      ((CochainComplex.singleFunctor (Systems.{c, v, max c v r} J B τ) 0).obj N))
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) (a : ((evaluation.{c, v, max c v r} J B τ m).obj M).val.obj U)
    (x : ((evaluation.{c, v, max c v r} J B τ m).obj N).val.obj U) (b : (B n).obj.obj U),
    ((ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U)
        ((ordinaryReduction.{c, v, r} J B τ A h
          (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r}
            J B τ) M N)).val.app U
          (b • scalarExtensionSection.{c, v, r} (coefficientMap.{c, v, max c v r} J B τ h)
            (A.scalar h)
            ((evaluation.{c, v, max c v r} J B τ m).obj
              (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v
                r} J B τ) M N)) U
            (((ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv.val.app U)
              (tensorSection.{c, v, r} J (B m) ((evaluation.{c, v, max c v r} J B τ m).obj M)
                ((evaluation.{c, v, max c v r} J B τ m).obj N) U a x)))) =
      tensorSection.{c, v, r} J (B n) ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N) U
        (((SemilinearSections.transition J B τ h).app M).val.app U a)
        (b • @id (((evaluation.{c, v, max c v r} J B τ n).obj N).val.obj U)
          (((SemilinearSections.transition J B τ h).app N).val.app U x))
  /-- The same tensor adjoint equation holds on whole-system cochain maps,
  before localization and before evaluating a derived morphism. -/
  cochain : ∀ (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    {m n : ℕ} (h : n ≤ m),
    (A.scalarTensorModel h).chain
        (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj P)
        (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj Q) ≫
      (operationScalarComplex.{c, v, r} J (coefficientMap.{c, v, max c v r} J B τ h) (A.scalar
        h)).map
        ((A.tensorEvaluationModel m).chain P Q) ≫
      cochainReduction.{c, v, r} J B τ A h
        ((totalTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B
          τ)).obj (P, Q)) =
    (totalTensor.{c, v, r} J (B n)).map
        (Prod.mkHom (cochainReduction.{c, v, r} J B τ A h P) (cochainReduction.{c, v, r} J B τ A h
          Q)) ≫
      (A.tensorEvaluationModel n).chain P Q

structure OperationModelLaws (A : Data.{c, v, r} J B τ) : Prop where
  /-- One whole-system resolution resolves all components simultaneously. -/
  resolution : ∀ K : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ,
    ∃ (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) (q : P ⟶ K),
      QuasiIso q ∧
      CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ) P ∧
      flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) P ∧
      ∀ n : ℕ,
        CochainComplex.IsKFlatIndependentCoefficients (R := B n)
          (((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up
            ℤ)).obj P) ∧
        flatTerms.{c, v, r} J (B n) (((SemilinearSections.evaluation.{c, v, max c v r} J B τ
          n).mapHomologicalComplex (.up ℤ)).obj P)
  /-- Every further model can still be evaluated without losing K-flatness or flat terms. -/
  evaluation : ∀ P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ) P →
    flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) P →
    ∀ n : ℕ,
      CochainComplex.IsKFlatIndependentCoefficients (R := B n)
        (((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex
          (.up ℤ)).obj P) ∧
      flatTerms.{c, v, r} J (B n)
        (((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex
          (.up ℤ)).obj P)
  /-- Total tensor preserves the chosen whole-system representative class. -/
  tensor : ∀ (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ) Q →
    flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) P →
    flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) Q →
    CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ)
        ((totalTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B
          τ)).obj (P, Q)) ∧
      flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ)
        ((totalTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B
          τ)).obj (P, Q))
  /-- The same closure holds for evaluated tensor vertices. -/
  level_tensor : ∀ (n : ℕ) (P Q : CochainComplex (Mod.{c, v, max c v r} J (B n)) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := B n) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := B n) Q →
    flatTerms.{c, v, r} J (B n) P → flatTerms.{c, v, r} J (B n) Q →
    CochainComplex.IsKFlatIndependentCoefficients (R := B n)
        ((totalTensor.{c, v, r} J (B n)).obj (P, Q)) ∧
      flatTerms.{c, v, r} J (B n) ((totalTensor.{c, v, r} J (B n)).obj (P, Q))
  /-- Coefficient quotients preserve K-flatness AND flat terms, and their actual
  universal derived counit computes them. There is no quotient-flatness hypothesis. -/
  quotient : ∀ {m n : ℕ} (h : n ≤ m) (P : CochainComplex (Mod.{c, v, max c v r} J (B m)) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := B m) P →
    flatTerms.{c, v, r} J (B m) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := B n)
        ((operationScalarComplex.{c, v, r} J (coefficientMap.{c, v, max c v r} J B τ h) (A.scalar
          h)).obj P) ∧
      flatTerms.{c, v, r} J (B n) ((operationScalarComplex.{c, v, r} J (coefficientMap.{c, v, max
        c v r} J B τ h) (A.scalar h)).obj P) ∧
      IsIso ((operationScalarCounit.{c, v, r} J
        (coefficientMap.{c, v, max c v r} J B τ h) (A.scalar h)).app P)
```

## New

```lean
def operationTensorPureFormula (A : Data.{c, v, r} J B τ) : Prop :=
  ∀ (M N : Systems.{c, v, max c v r} J B τ)
    (_hM : flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ)
      ((CochainComplex.singleFunctor (Systems.{c, v, max c v r} J B τ) 0).obj M))
    (_hN : flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ)
      ((CochainComplex.singleFunctor (Systems.{c, v, max c v r} J B τ) 0).obj N))
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) (a : ((evaluation.{c, v, max c v r} J B τ m).obj M).val.obj U)
    (x : ((evaluation.{c, v, max c v r} J B τ m).obj N).val.obj U) (b : (B n).obj.obj U),
    ((ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U)
        ((ordinaryReduction.{c, v, r} J B τ A h
          (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r}
            J B τ) M N)).val.app U
          (b • scalarExtensionSection.{c, v, r} (coefficientMap.{c, v, max c v r} J B τ h)
            (A.scalar h)
            ((evaluation.{c, v, max c v r} J B τ m).obj
              (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v
                r} J B τ) M N)) U
            (((ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv.val.app U)
              (tensorSection.{c, v, r} J (B m) ((evaluation.{c, v, max c v r} J B τ m).obj M)
                ((evaluation.{c, v, max c v r} J B τ m).obj N) U a x)))) =
      tensorSection.{c, v, r} J (B n) ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N) U
        (((SemilinearSections.transition J B τ h).app M).val.app U a)
        (b • @id (((evaluation.{c, v, max c v r} J B τ n).obj N).val.obj U)
          (((SemilinearSections.transition J B τ h).app N).val.app U x))

def operationTensorCochainFormula (A : Data.{c, v, r} J B τ) : Prop :=
  ∀ (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    {m n : ℕ} (h : n ≤ m),
    (A.scalarTensorModel h).chain
        (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj P)
        (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj Q) ≫
      (operationScalarComplex.{c, v, r} J (coefficientMap.{c, v, max c v r} J B τ h) (A.scalar
        h)).map
        ((A.tensorEvaluationModel m).chain P Q) ≫
      cochainReduction.{c, v, r} J B τ A h
        ((totalTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B
          τ)).obj (P, Q)) =
    (totalTensor.{c, v, r} J (B n)).map
        (Prod.mkHom (cochainReduction.{c, v, r} J B τ A h P) (cochainReduction.{c, v, r} J B τ A h
          Q)) ≫
      (A.tensorEvaluationModel n).chain P Q

structure OperationTensorLaws (A : Data.{c, v, r} J B τ) : Prop where
  /-- Tensor preserves normalization. -/
  normalized : ∀ (M N : DS.{c, v, max c v r} J B τ),
    Normalized.{c, v, max c v r} J B τ A.scalar M → Normalized.{c, v, max c v r} J B τ A.scalar N →
      Normalized.{c, v, max c v r} J B τ A.scalar (A.closed.tensor.obj (M, N))
  /-- The adjoint of the actual tensor transition is monoidal scalar extension
  followed by the tensor of the two original adjoints. -/
  transition : ∀ (M N : DS.{c, v, max c v r} J B τ) {m n : ℕ} (h : n ≤ m),
    reduction.{c, v, max c v r} J B τ h (A.scalar h) (A.closed.tensor.obj (M, N)) ≫
        (A.tensorEvaluation n).hom.app (M, N) =
      (A.scalar h).T.map ((A.tensorEvaluation m).hom.app (M, N)) ≫
        (A.scalarTensor h).hom.app ((e.{c, v, max c v r} J B τ m).obj M, (e.{c, v, max c v r} J B
          τ m).obj N) ≫
        (A.levelClosed n).tensor.map
          (Prod.mkHom (reduction.{c, v, max c v r} J B τ h (A.scalar h) M)
            (reduction.{c, v, max c v r} J B τ h (A.scalar h) N))
  /-- The actual input transition factors through its scalar-insertion unit. -/
  input_factor : ∀ (M : DS.{c, v, max c v r} J B τ) {m n : ℕ} (h : n ≤ m),
    (derivedTransition.{c, v, max c v r} J B τ h).app M =
      (A.scalar h).adjunction.unit.app ((e.{c, v, max c v r} J B τ m).obj M) ≫
        (resD.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)).map (reduction.{c, v,
          max c v r} J B τ h (A.scalar h) M)
  /-- Successive output adjoints equal the direct output adjoint. -/
  cocycle : ∀ (M N : DS.{c, v, max c v r} J B τ)
    {k m n : ℕ} (h : n ≤ m) (j : m ≤ k),
    (A.scalar h).T.map
        (reduction.{c, v, max c v r} J B τ j (A.scalar j) (A.closed.tensor.obj (M, N))) ≫
        reduction.{c, v, max c v r} J B τ h (A.scalar h) (A.closed.tensor.obj (M, N)) =
      (A.scalarComposition h j).hom.app
          ((e.{c, v, max c v r} J B τ k).obj (A.closed.tensor.obj (M, N))) ≫
        reduction.{c, v, max c v r} J B τ (h.trans j) (A.scalar (h.trans j)) (A.closed.tensor.obj
          (M, N))
  /-- On local flat representatives the scalar adjoint uses the actual transitions,
  sending (a tensor x) tensor b to tau(a) tensor b tau(x). -/
  pure : operationTensorPureFormula.{c, v, r} J B τ A
  /-- The same tensor adjoint equation holds on whole-system cochain maps,
  before localization and before evaluating a derived morphism. -/
  cochain : operationTensorCochainFormula.{c, v, r} J B τ A

def operationModelQuotientFormula (A : Data.{c, v, r} J B τ) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m) (P : CochainComplex (Mod.{c, v, max c v r} J (B m)) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := B m) P →
    flatTerms.{c, v, r} J (B m) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := B n)
        ((operationScalarComplex.{c, v, r} J (coefficientMap.{c, v, max c v r} J B τ h) (A.scalar
          h)).obj P) ∧
      flatTerms.{c, v, r} J (B n) ((operationScalarComplex.{c, v, r} J (coefficientMap.{c, v, max
        c v r} J B τ h) (A.scalar h)).obj P) ∧
      IsIso ((operationScalarCounit.{c, v, r} J
        (coefficientMap.{c, v, max c v r} J B τ h) (A.scalar h)).app P)

structure OperationModelLaws (A : Data.{c, v, r} J B τ) : Prop where
  /-- One whole-system resolution resolves all components simultaneously. -/
  resolution : ∀ K : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ,
    ∃ (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) (q : P ⟶ K),
      QuasiIso q ∧
      CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ) P ∧
      flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) P ∧
      ∀ n : ℕ,
        CochainComplex.IsKFlatIndependentCoefficients (R := B n)
          (((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up
            ℤ)).obj P) ∧
        flatTerms.{c, v, r} J (B n) (((SemilinearSections.evaluation.{c, v, max c v r} J B τ
          n).mapHomologicalComplex (.up ℤ)).obj P)
  /-- Every further model can still be evaluated without losing K-flatness or flat terms. -/
  evaluation : ∀ P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ) P →
    flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) P →
    ∀ n : ℕ,
      CochainComplex.IsKFlatIndependentCoefficients (R := B n)
        (((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex
          (.up ℤ)).obj P) ∧
      flatTerms.{c, v, r} J (B n)
        (((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex
          (.up ℤ)).obj P)
  /-- Total tensor preserves the chosen whole-system representative class. -/
  tensor : ∀ (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ) Q →
    flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) P →
    flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) Q →
    CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ)
        ((totalTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B
          τ)).obj (P, Q)) ∧
      flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ)
        ((totalTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B
          τ)).obj (P, Q))
  /-- The same closure holds for evaluated tensor vertices. -/
  level_tensor : ∀ (n : ℕ) (P Q : CochainComplex (Mod.{c, v, max c v r} J (B n)) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := B n) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := B n) Q →
    flatTerms.{c, v, r} J (B n) P → flatTerms.{c, v, r} J (B n) Q →
    CochainComplex.IsKFlatIndependentCoefficients (R := B n)
        ((totalTensor.{c, v, r} J (B n)).obj (P, Q)) ∧
      flatTerms.{c, v, r} J (B n) ((totalTensor.{c, v, r} J (B n)).obj (P, Q))
  /-- Coefficient quotients preserve K-flatness AND flat terms, and their actual
  universal derived counit computes them. There is no quotient-flatness hypothesis. -/
  quotient : operationModelQuotientFormula.{c, v, r} J B τ A
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NormalizedOperationSystemModels | J6 | Its complete proofs use exactly the original formulas through definitional unfolding. |

`tools/downstream.py Sheaf.Paper.NormalizedOperationSystemModels --uses OperationTensorLaws` and the same command for `OperationModelLaws` report no downstream modules and only this module as a user. A shared source search agrees. The three formula names are new and have no existing users. The existing DAG node and all its mathematical dependencies are unchanged; these are names for its original field formulas. No source-library edit or forced adaptation is required.

The complete three-module sandbox subsequently compiled cleanly; the full item module took 37.2 seconds under the unchanged 60-second limit.

## Status

landed 20261022T011850-L-3225647 2026-10-22 (merge of deliver/J6/Sheaf.Paper.NormalizedOperationSystemModels)
