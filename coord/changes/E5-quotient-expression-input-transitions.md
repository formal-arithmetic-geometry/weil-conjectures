# WeilConjectures.StrictQuotient.quotientExpressionKFlatOperations

## Reason

STATEMENT-DISPUTED (old signature): levelwise K-flatness and flat terms do not force
normalization of arbitrary horizontal maps. For example take E = ℚ_l, Z = X = Y = Spec ℚ, h = f = id, and one input.
The finite constant coefficient sheaves are nonzero. Take the rank-one coefficient module
in degree zero at every level and zero maps between unequal levels. Identities
remain identities; composition holds. Tensor and inverse-image expressions are
levelwise flat and K-flat. For two unequal positive levels with nonzero coefficient
rings the ordinary transition adjunct is zero between nonzero rank-one modules,
so is not invertible. The strict quotient model construction instead supplies
actual quotient transitions. The prior split lost precisely this compatibility.

Restore the original input complexes P and the level identifications κ and
compatibility hκ produced by quotientExpressionKFlatModels in the sole caller. This is the
source's actual-quotient condition, not a target statement change. No definition
changes and no target meaning changes.

## Old

```lean
theorem quotientExpressionKFlatOperations
    {Z X Y : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (r : ℕ) (N : Fin r → Complex l E Y)
    (hgood : ∀ (W : Scheme.{t}) (K : Complex l E W), Generated l E h f N W K →
      ∀ n : ℕ, Good l E K n) :
    (∀ (W : Scheme.{t}) (K : Complex l E W), Generated l E h f N W K →
      IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj K) ∧
      (∀ (S : CoefficientDerivedSystemTensors l E W)
        (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m),
        ∃ hK : CochainComplex.IsKFlatIndependentCoefficients
          (R := integralCoefficientCommRingSheaf l E W m) (level l E K m),
          AdjointModel l E K S D hmn hK)) ∧
    (∀ (W : Scheme.{t}) (U V : Complex l E W),
      Generated l E h f N W U → Generated l E h f N W V →
      TensorTransitions l E U V ∧
      (∀ (n : ℕ) (S : CoefficientDerivedSystemTensors l E W),
        ∃ (hU : Good l E U n) (hV : Good l E V n)
          (e : DerivedCategory.Q.obj (level l E (total l E U V) n) ≅
            (S.finiteClosed n).tensor.obj
              (DerivedCategory.Q.obj (level l E U n), DerivedCategory.Q.obj (level l E V n))),
          e.hom = DerivedCategory.Q.map (coefficientEvaluationTensorIso l E W n U V).hom ≫
            ((S.finiteTensorModel n).iso (Scheme.ProEt.topology W)
              (integralCoefficientCommRingSheaf l E W n) (S.finiteClosed n)
              (level l E U n) (level l E V n) hU.1 hV.1).hom) ∧
      (∀ (S : CoefficientDerivedSystemTensors l E W)
        (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m)
        (hUm : Good l E U m) (hVm : Good l E V m)
        (hUn : Good l E U n) (hVn : Good l E V n),
        TensorAdjointEquation l E U V S D hmn hUm hVm hUn hVn)) ∧
    (∀ {V W : Scheme.{t}} (g : V ⟶ W), AllowedArrow h f g →
      ∀ K : Complex l E W, Generated l E h f N W K →
        PullbackTransitions l E g K ∧
        (∀ n : ℕ, PullbackModel l E g K n ∧ PullbackComputes l E g K n) ∧
        (∀ (SW : CoefficientDerivedSystemTensors l E W)
          (DW : CoefficientFiniteQuotientCalculus l E W SW)
          (SV : CoefficientDerivedSystemTensors l E V)
          (DV : CoefficientFiniteQuotientCalculus l E V SV) {m n : ℕ} (hmn : n ≤ m),
          PullbackAdjointEquation l E g K SW DW SV DV hmn))
```

## New

```lean
theorem quotientExpressionKFlatOperations
    {Z X Y : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (r : ℕ) (N : Fin r → Complex l E Y)
    (P : Fin r → CochainComplex (scalarReductionSource l E Y) ℤ)
    (κ : ∀ (i : Fin r) (n : ℕ), level l E (N i) n ≅
      ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj (P i))
    (hκ : ∀ (i : Fin r) {m n : ℕ} (hmn : n ≤ m),
      transition l E (N i) hmn ≫
          ((normalizedDVRModuleRes l E Y hmn).mapHomologicalComplex (.up ℤ)).map
            (κ i n).hom =
        (κ i m).hom ≫
          (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E Y hmn)
            (.up ℤ)).app (P i))
    (hgood : ∀ (W : Scheme.{t}) (K : Complex l E W), Generated l E h f N W K →
      ∀ n : ℕ, Good l E K n) :
    (∀ (W : Scheme.{t}) (K : Complex l E W), Generated l E h f N W K →
      IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj K) ∧
      (∀ (S : CoefficientDerivedSystemTensors l E W)
        (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m),
        ∃ hK : CochainComplex.IsKFlatIndependentCoefficients
          (R := integralCoefficientCommRingSheaf l E W m) (level l E K m),
          AdjointModel l E K S D hmn hK)) ∧
    (∀ (W : Scheme.{t}) (U V : Complex l E W),
      Generated l E h f N W U → Generated l E h f N W V →
      TensorTransitions l E U V ∧
      (∀ (n : ℕ) (S : CoefficientDerivedSystemTensors l E W),
        ∃ (hU : Good l E U n) (hV : Good l E V n)
          (e : DerivedCategory.Q.obj (level l E (total l E U V) n) ≅
            (S.finiteClosed n).tensor.obj
              (DerivedCategory.Q.obj (level l E U n), DerivedCategory.Q.obj (level l E V n))),
          e.hom = DerivedCategory.Q.map (coefficientEvaluationTensorIso l E W n U V).hom ≫
            ((S.finiteTensorModel n).iso (Scheme.ProEt.topology W)
              (integralCoefficientCommRingSheaf l E W n) (S.finiteClosed n)
              (level l E U n) (level l E V n) hU.1 hV.1).hom) ∧
      (∀ (S : CoefficientDerivedSystemTensors l E W)
        (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m)
        (hUm : Good l E U m) (hVm : Good l E V m)
        (hUn : Good l E U n) (hVn : Good l E V n),
        TensorAdjointEquation l E U V S D hmn hUm hVm hUn hVn)) ∧
    (∀ {V W : Scheme.{t}} (g : V ⟶ W), AllowedArrow h f g →
      ∀ K : Complex l E W, Generated l E h f N W K →
        PullbackTransitions l E g K ∧
        (∀ n : ℕ, PullbackModel l E g K n ∧ PullbackComputes l E g K n) ∧
        (∀ (SW : CoefficientDerivedSystemTensors l E W)
          (DW : CoefficientFiniteQuotientCalculus l E W SW)
          (SV : CoefficientDerivedSystemTensors l E V)
          (DV : CoefficientFiniteQuotientCalculus l E V SV) {m n : ℕ} (hmn : n ≤ m),
          PullbackAdjointEquation l E g K SW DW SV DV hmn))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QuotientExpressionKFlatOperations | E5 | Restore actual quotient input data; prove the corrected theorem by constructor induction and adjunction calculations. |
| Sheaf.Paper.QuotientExpressionKFlatNormalization | unclaimed | Forward existing P, κ and hκ to the repaired theorem; its statement, visibility and public imports stay identical. |

The direct Lean use search and DAG citer audit find only the parent above. The
blueprint unit has no realized statement or proof-step attachment requiring the
incorrect generalization. The adapted caller is compiled against the repaired dependency. Its full
public signature is compared verbatim with the original. The only body change
is forwarding P, κ and hκ in the existing call.

## Status

landed 20261026T065545-L-3078776 2026-10-26 (merge of deliver/E5/Sheaf.Paper.QuotientExpressionKFlatOperations)
