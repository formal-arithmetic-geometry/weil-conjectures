# WeilConjectures.CoefficientDerivedSystemFibers

## Reason

The resolution-model proof already constructs `CoefficientDerivedSystemTensorCoherence`,
then transports it to the normalized reduction record. It used that proof to construct
internal-Hom fibers but discarded it when constructing `CoefficientDerivedSystemFibers`.
Consequently the chosen `finiteIntrinsicClosed` and `finiteIntrinsicTensorModels` exposed
no equation relating their associator to signed total tensor. Closed adjunction and
binary evaluation normalization alone do not specify that associator.

Retain the finite component as a proof field (`Exists` and `Nonempty`), without making
a new data choice. The same existing `hTR` supplies it. All existing data fields,
projections, theorem binders, and target statement texts stay as written.

This is a definition change used by targets: their semantic statement review must be
reopened for the affected finite closed/tensor definitions. The added normalization is
the native derived tensor normalization of Stacks 0FPT, 06YU and 07A4.

## Old

```lean
structure CoefficientDerivedSystemFibers extends CoefficientDerivedSystemReduction l E W where
  /-- Reduction's tensor comparison has the simultaneous strict representative formula. -/
  reductionTensor_normalization : CoefficientReductionTensorNormalization l E W
    toCoefficientDerivedSystemReduction
  /-- Finite tensor comparisons have their ordinary generator normalization. -/
  finiteTensor_normalization : CoefficientFiniteTensorNormalization l E W
    toCoefficientDerivedSystemReduction
  /-- Evaluation tensor comparisons have their simultaneous representative normalization. -/
  evaluationTensor_normalization : CoefficientEvaluationTensorNormalization l E W
    toCoefficientDerivedSystemReduction
  /-- Reduction uses precisely the normalized finite tensor comparisons at each level. -/
  reductionTensor_evaluation : CoefficientReductionTensorEvaluation l E W
    toCoefficientDerivedSystemReduction

  /-- Actual quotient scalar extension with its adjunction and K-flat tensor normalization. -/
  quotientCalculus : CoefficientFiniteQuotientCalculus l E W toCoefficientDerivedSystemTensors

  /-- Beta preserves evaluation, transposes and internal composition as system maps. -/
  reduction_compatible : CoefficientEvaluationCompatible integralClosed systemClosed
    reduction reductionTensor
  /-- Finite comparisons use the same evaluation-defined tensor-Hom calculus. -/
  finite_compatible : ∀ n : ℕ, CoefficientEvaluationCompatible integralClosed (finiteClosed n)
    (coefficientFiniteDerivedExtension l E W n) (finiteTensor n)
  /-- Internal Hom on normalized inputs has exactly the finite internal-Hom fibers. -/
  fiberHom : ∀ (M N : coefficientSequenceDerived l E W),
    IsNormalizedCoefficientSequence l E W M → IsNormalizedCoefficientSequence l E W N →
    ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E W n).obj
          ((coefficientSequenceInternalHom l E W).obj (op M, N)) ≅
        (coefficientFiniteInternalHom l E W n).obj
          (op ((coefficientSequenceDerivedEvaluation l E W n).obj M),
            (coefficientSequenceDerivedEvaluation l E W n).obj N)
  /-- The fiber identification is induced by simultaneous system evaluation. -/
  fiber_evaluation : ∀ (M N : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M)
    (hN : IsNormalizedCoefficientSequence l E W N) (n : ℕ),
    (evaluationTensor n).inv.app
        ((coefficientSequenceInternalHom l E W).obj (op M, N), M) ≫
      (coefficientSequenceDerivedEvaluation l E W n).map (systemClosed.evaluation M N) =
    (finiteClosed n).tensor.map
        (Prod.mkHom ((fiberHom M N hM hN n).hom) (𝟙 _)) ≫
      (finiteClosed n).evaluation
        ((coefficientSequenceDerivedEvaluation l E W n).obj M)
        ((coefficientSequenceDerivedEvaluation l E W n).obj N)
  /-- Fiberwise internal Hom is natural for input derived morphisms. -/
  fiber_naturality : ∀ (M N M' N' : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M)
    (hN : IsNormalizedCoefficientSequence l E W N)
    (hM' : IsNormalizedCoefficientSequence l E W M')
    (hN' : IsNormalizedCoefficientSequence l E W N') (f : M' ⟶ M) (g : N ⟶ N') (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E W n).map
        ((coefficientSequenceInternalHom l E W).map
        (Prod.mkHom (f.op) (g))) ≫
      (fiberHom M' N' hM' hN' n).hom =
    (fiberHom M N hM hN n).hom ≫ (coefficientFiniteInternalHom l E W n).map
      (Prod.mkHom (((coefficientSequenceDerivedEvaluation l E W n).map f).op)
        ((coefficientSequenceDerivedEvaluation l E W n).map g))
  /-- The adjunct of the actual `coefficientSequenceDerivedTransition` on internal Hom,
  under `fiberHom` at m and n, is c_(m,n) followed by RHom(alpha_M inverse, alpha_N).
  Here c_(m,n) transposes reduced finite evaluation using `quotientCalculus.tensor`,
  whose `tensor_model` fixes its comparison on every pair of K-flat representatives. -/
  fiber_transition : CoefficientFiberTransition l E W toCoefficientDerivedSystemTensors
    quotientCalculus fiberHom
  /-- Beta evaluates to the usual finite internal-Hom reduction comparison. -/
  beta_evaluation : ∀ (P Q : DerivedCategory (scalarReductionSource l E W)) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E W n).map
        (coefficientBaseChangeHom integralClosed systemClosed reduction reductionTensor P Q) ≫
      (fiberHom _ _ (reduction_normalized P) (reduction_normalized Q) n).hom =
    (reductionEvaluation n).hom.app ((coefficientIntegralInternalHom l E W).obj (op P, Q)) ≫
      coefficientBaseChangeHom integralClosed (finiteClosed n)
        (coefficientFiniteDerivedExtension l E W n) (finiteTensor n) P Q ≫
      (coefficientFiniteInternalHom l E W n).map
        (Prod.mkHom (((reductionEvaluation n).hom.app P).op) ((reductionEvaluation n).inv.app Q))
  /-- Joint conservativity on actual derived system maps. -/
  isIso_iff_evaluations : ∀ {M N : coefficientSequenceDerived l E W} (f : M ⟶ N),
    IsIso f ↔ ∀ n : ℕ, IsIso ((coefficientSequenceDerivedEvaluation l E W n).map f)
  /-- Total derived global sections of a system retain its finite fibers. -/
  globalEvaluation : ∀ (M N : coefficientSequenceDerived l E W),
    IsNormalizedCoefficientSequence l E W M → IsNormalizedCoefficientSequence l E W N →
    ∀ n : ℕ,
      (coefficientMappingEvaluation.{max u (t+1)} n).obj
          ((coefficientSequenceGlobalHom l E W).obj (op M, N)) ≅
        (coefficientFiniteGlobalHom l E W n).obj
          (op ((coefficientSequenceDerivedEvaluation l E W n).obj M),
            (coefficientSequenceDerivedEvaluation l E W n).obj N)
```

## New

```lean
structure CoefficientDerivedSystemFibers extends CoefficientDerivedSystemReduction l E W where
  /-- Retain the finite constraint witnesses used to construct the tensor models. -/
  finite_tensor_coherence : ∀ n : ℕ,
    ∃ β : @SymmetricCategory (normalizedDVRDerived l E W n) _ (finiteClosed n).monoidal,
      Nonempty (RingedDerivedTensorCoherence.{t+1, t, u} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) (finiteClosed n) (finiteTensorModel n) β)
  /-- Reduction's tensor comparison has the simultaneous strict representative formula. -/
  reductionTensor_normalization : CoefficientReductionTensorNormalization l E W
    toCoefficientDerivedSystemReduction
  /-- Finite tensor comparisons have their ordinary generator normalization. -/
  finiteTensor_normalization : CoefficientFiniteTensorNormalization l E W
    toCoefficientDerivedSystemReduction
  /-- Evaluation tensor comparisons have their simultaneous representative normalization. -/
  evaluationTensor_normalization : CoefficientEvaluationTensorNormalization l E W
    toCoefficientDerivedSystemReduction
  /-- Reduction uses precisely the normalized finite tensor comparisons at each level. -/
  reductionTensor_evaluation : CoefficientReductionTensorEvaluation l E W
    toCoefficientDerivedSystemReduction

  /-- Actual quotient scalar extension with its adjunction and K-flat tensor normalization. -/
  quotientCalculus : CoefficientFiniteQuotientCalculus l E W toCoefficientDerivedSystemTensors

  /-- Beta preserves evaluation, transposes and internal composition as system maps. -/
  reduction_compatible : CoefficientEvaluationCompatible integralClosed systemClosed
    reduction reductionTensor
  /-- Finite comparisons use the same evaluation-defined tensor-Hom calculus. -/
  finite_compatible : ∀ n : ℕ, CoefficientEvaluationCompatible integralClosed (finiteClosed n)
    (coefficientFiniteDerivedExtension l E W n) (finiteTensor n)
  /-- Internal Hom on normalized inputs has exactly the finite internal-Hom fibers. -/
  fiberHom : ∀ (M N : coefficientSequenceDerived l E W),
    IsNormalizedCoefficientSequence l E W M → IsNormalizedCoefficientSequence l E W N →
    ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E W n).obj
          ((coefficientSequenceInternalHom l E W).obj (op M, N)) ≅
        (coefficientFiniteInternalHom l E W n).obj
          (op ((coefficientSequenceDerivedEvaluation l E W n).obj M),
            (coefficientSequenceDerivedEvaluation l E W n).obj N)
  /-- The fiber identification is induced by simultaneous system evaluation. -/
  fiber_evaluation : ∀ (M N : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M)
    (hN : IsNormalizedCoefficientSequence l E W N) (n : ℕ),
    (evaluationTensor n).inv.app
        ((coefficientSequenceInternalHom l E W).obj (op M, N), M) ≫
      (coefficientSequenceDerivedEvaluation l E W n).map (systemClosed.evaluation M N) =
    (finiteClosed n).tensor.map
        (Prod.mkHom ((fiberHom M N hM hN n).hom) (𝟙 _)) ≫
      (finiteClosed n).evaluation
        ((coefficientSequenceDerivedEvaluation l E W n).obj M)
        ((coefficientSequenceDerivedEvaluation l E W n).obj N)
  /-- Fiberwise internal Hom is natural for input derived morphisms. -/
  fiber_naturality : ∀ (M N M' N' : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M)
    (hN : IsNormalizedCoefficientSequence l E W N)
    (hM' : IsNormalizedCoefficientSequence l E W M')
    (hN' : IsNormalizedCoefficientSequence l E W N') (f : M' ⟶ M) (g : N ⟶ N') (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E W n).map
        ((coefficientSequenceInternalHom l E W).map
        (Prod.mkHom (f.op) (g))) ≫
      (fiberHom M' N' hM' hN' n).hom =
    (fiberHom M N hM hN n).hom ≫ (coefficientFiniteInternalHom l E W n).map
      (Prod.mkHom (((coefficientSequenceDerivedEvaluation l E W n).map f).op)
        ((coefficientSequenceDerivedEvaluation l E W n).map g))
  /-- The adjunct of the actual `coefficientSequenceDerivedTransition` on internal Hom,
  under `fiberHom` at m and n, is c_(m,n) followed by RHom(alpha_M inverse, alpha_N).
  Here c_(m,n) transposes reduced finite evaluation using `quotientCalculus.tensor`,
  whose `tensor_model` fixes its comparison on every pair of K-flat representatives. -/
  fiber_transition : CoefficientFiberTransition l E W toCoefficientDerivedSystemTensors
    quotientCalculus fiberHom
  /-- Beta evaluates to the usual finite internal-Hom reduction comparison. -/
  beta_evaluation : ∀ (P Q : DerivedCategory (scalarReductionSource l E W)) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E W n).map
        (coefficientBaseChangeHom integralClosed systemClosed reduction reductionTensor P Q) ≫
      (fiberHom _ _ (reduction_normalized P) (reduction_normalized Q) n).hom =
    (reductionEvaluation n).hom.app ((coefficientIntegralInternalHom l E W).obj (op P, Q)) ≫
      coefficientBaseChangeHom integralClosed (finiteClosed n)
        (coefficientFiniteDerivedExtension l E W n) (finiteTensor n) P Q ≫
      (coefficientFiniteInternalHom l E W n).map
        (Prod.mkHom (((reductionEvaluation n).hom.app P).op) ((reductionEvaluation n).inv.app Q))
  /-- Joint conservativity on actual derived system maps. -/
  isIso_iff_evaluations : ∀ {M N : coefficientSequenceDerived l E W} (f : M ⟶ N),
    IsIso f ↔ ∀ n : ℕ, IsIso ((coefficientSequenceDerivedEvaluation l E W n).map f)
  /-- Total derived global sections of a system retain its finite fibers. -/
  globalEvaluation : ∀ (M N : coefficientSequenceDerived l E W),
    IsNormalizedCoefficientSequence l E W M → IsNormalizedCoefficientSequence l E W N →
    ∀ n : ℕ,
      (coefficientMappingEvaluation.{max u (t+1)} n).obj
          ((coefficientSequenceGlobalHom l E W).obj (op M, N)) ≅
        (coefficientFiniteGlobalHom l E W n).obj
          (op ((coefficientSequenceDerivedEvaluation l E W n).obj M),
            (coefficientSequenceDerivedEvaluation l E W n).obj N)
```

`CoefficientDerivedSystemEvaluationData` additionally publicly imports
`Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal` for the field's type.
The constructor in `CoefficientDerivedSystemResolutionModels` adds exactly:

```lean
      finite_tensor_coherence := by
        unfold CoefficientDerivedSystemTensorCoherence at hTR
        exact hTR.2.2
```

## Users

The current claim records list no holder for either repaired module. The table combines
all direct importers with the modules reported by `tools/downstream.py --uses
CoefficientDerivedSystemFibers`; the assigned item is also included. The transitive
closure contains many modules, but only these named users and direct importers need
source adaptation or interface checks for this added proof field.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientDerivedSystemResolutionModels | unclaimed | Adds the retained finite witness from hTR; compiled. |
| Sheaf.Paper.CoefficientNormalizedReductionModels | unclaimed | Direct importer; compiles unchanged. |
| Sheaf.Paper.CoefficientDerivedSectionsNormalization | unclaimed | Direct importer; compiles unchanged. |
| Sheaf.Paper.CoefficientDerivedSystemHomProjectionTransport | unclaimed | Direct importer; compiles unchanged. |
| Sheaf.Paper.CoefficientDerivedSystemGammaProjectionTransport | unclaimed | Direct importer; compiles unchanged. |
| Sheaf.Paper.CoefficientDerivedSystemProjectionFormulas | unclaimed | Direct importer; compiles unchanged. |
| Sheaf.Paper.CoefDerivedSystemEvaluationCalculus | unclaimed | Direct importer of both changed modules; compiles unchanged. |
| Sheaf.Paper.FiniteCounitRestrictionTowers | unclaimed | Indirect named user of Fibers; compiles unchanged. |
| Sheaf.Paper.FiniteRestrictionConstructibleVertices | unclaimed | Indirect named user of Fibers; compiles unchanged. |
| Sheaf.Paper.FiniteRestrictionDiagramNaturality | unclaimed | Indirect named user of Fibers; compiles unchanged. |
| Sheaf.Paper.CoefficientDerivedSystemEvaluationData | unclaimed | Declares Fibers and extends it to Calculus; compiled. |
| Sheaf.Paper.FinitePullbackTensorAssociativityRepresentatives | G2 | Assigned item; uses the retained witness for its associator normalization. |
| Sheaf.Paper.CanonicalIntegralEvaluationCalculus | Y3 landed; currently unclaimed | Forced adaptation: supply finite_tensor_coherence for the transported finite closed structure and tensor model; compiles in 27.6 s. |
| Sheaf.Paper.CanonicalCoefficientRepresentativeLaws | Y3 landed; currently unclaimed | Reviewer-requested compatibility check; source unchanged, compiled. |
| Sheaf.Paper.CanonicalCoefficientCompositionLaws | Y3 landed; currently unclaimed | Reviewer-requested compatibility check; source unchanged, compiled. |
| Sheaf.Paper.CanonicalCoefficientReduction | unchanged compatibility check | Current direct importer; compiled unchanged. |
| Sheaf.Paper.CoefficientDerivedSystemGammaProjectionTransportFinal | unchanged compatibility check | Current direct importer; compiled unchanged. |
| Sheaf.Paper.CoefficientNormalizedReductionCore | unchanged compatibility check | Current direct importer; compiled unchanged. |
| Sheaf.Paper.CoefficientDerivedSectionsScalarHomZero | unchanged compatibility check | Current direct importer; compiled unchanged. |
| Sheaf.Paper.CoefficientNormalizedReductionNormalizations | unchanged compatibility check | Current direct importer; compiled unchanged. |
| Sheaf.Paper.CoefficientTensorModelComparison | unchanged compatibility check | Current direct importer; compiled unchanged. |
| Sheaf.Paper.CoefficientDerivedSectionsCore | unchanged compatibility check | Current direct importer; compiled unchanged. |

## Returned delivery repair (C-89dfb, point 2b)

Compared the retained sandbox with the refreshed shared main sources. The existing
EvaluationData and ResolutionModels edits remain exactly the import/proof-field
addition and constructor witness above. The three original existing-node changes
have no unrelated differences from current main. The newly landed canonical
calculus is copied from current main and adapted only where the field addition
requires it.

Original failure in `CanonicalIntegralEvaluationCalculus.lean:88:41`:
`Fields missing: finite_tensor_coherence` in private definition `CanonicalCoefficient.fibers`.
The published original compiles with the old fiber record. The change adds a
private proved tensor-model uniqueness helper, proof-only imports of the existing
Hom-representative surjectivity and generator/constraint APIs, and the missing
proof field (the field begins at line 141 in the adapted file). Uncurrying into
a fixed Hom resolution and pure-tensor uniqueness
identify the transported model with the fixed normalized duality model. Its
constraint-completion witness then supplies precisely the required coherence.
There is no new data choice or arbitrary coherence assumption. Existing public
signatures, attributes, visibility and public imports remain identical.

The canonical reduction, representative laws, composition laws and adapted calculus
compiled in import order against the changed fiber record (0.1 s, 43.0 s, 3.6 s,
27.6 s respectively); the assigned theorem compiled again in 24.8 s.
The representative and composition-law modules are checked unchanged against the
updated fiber record. All 14 current direct importers of the two repaired coefficient modules also
compiled successfully, each within 60 s. Their unchanged temporary compile copies
have been removed and are not delivered.
The composition-law module's pre-existing named theorem hole is untouched.

## Status

landed 20261028T034751-L-3542786 2026-10-28 (merge of deliver/G2/Sheaf.Paper.FinitePullbackTensorAssociativityRepresentatives)
