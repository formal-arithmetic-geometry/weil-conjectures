# WeilConjectures.RationalSmoothPurityCanonical.tensorAugmentation_existsUnique

## Reason

The original inline specification caused repeated large kernel checks: profiling
reported 18.69 seconds checking this theorem alone, and the complete module
exceeded the 60-second limit. Name the identical conjunction as the public
predicate `TensorAugmentationNormalized` in the same module. It has no proof
holes and is attached to the existing definition node. The theorem now refers
to that predicate. Its expanded statement and selected augmentation are
unchanged, including both the pure-tensor first coordinate and the zero second
coordinate. The module compiles in 56.8 seconds after this refactor.

No target meaning changes. This adds no theorem, axiom, construction witness,
or split-off obligation; it packages the existing proposition definitionally.
Local transparency and instance priorities do not affect importers.

## Old

```lean
theorem tensorAugmentation_existsUnique (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    ∃! eta : ordinaryTotal l E T ⟶ integralOperationsTensorComplexFunctor l E T,
      (∀ (P Q : CochainComplex (integralTowerModules l E T) ℤ)
        (p q : ℤ) (n : ℕ) (U : T.ProEtᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (((eta.app (P,Q)).f (p + q) ≫
          (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism
              (K := fun j ↦ ((integralOperationsTensorTowerFunctor l E T).obj
                (P,Q)).obj (op j))
              (integralOperationsTowerStep
                ((integralOperationsTensorTowerFunctor l E T).obj (P,Q))))).f (p + q) ≫
          (Pi.π (fun j ↦ ((integralOperationsTensorTowerFunctor l E T).obj
            (P,Q)).obj (op j)) n).f (p + q)).val.app U)
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology T)
              (completedIntegralCommRingSheafUnrestricted l E T) P Q p q (p+q) rfl U x y) =
          integralOperationsTotalTensorSection l E T n P Q p q U
            (unrestrictedIntegralTensorSection l E T n (P.X p) U 1 x)
            (unrestrictedIntegralTensorSection l E T n (Q.X q) U 1 y)) ∧
      ∀ (P Q : CochainComplex (integralTowerModules l E T) ℤ) (i : ℤ),
        (eta.app (P,Q)).f i ≫
          (CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism
              (K := fun j ↦ ((integralOperationsTensorTowerFunctor l E T).obj
                (P,Q)).obj (op j))
              (integralOperationsTowerStep
                ((integralOperationsTensorTowerFunctor l E T).obj (P,Q))))).v
                  i (i - 1) (by omega) = 0 := by
  sorry
```

## New

```lean
def TensorAugmentationNormalized (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (eta : ordinaryTotal l E T ⟶ integralOperationsTensorComplexFunctor l E T) : Prop :=
      (∀ (P Q : CochainComplex (integralTowerModules l E T) ℤ)
        (p q : ℤ) (n : ℕ) (U : T.ProEtᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (((eta.app (P,Q)).f (p + q) ≫
          (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism
              (K := fun j ↦ ((integralOperationsTensorTowerFunctor l E T).obj
                (P,Q)).obj (op j))
              (integralOperationsTowerStep
                ((integralOperationsTensorTowerFunctor l E T).obj (P,Q))))).f (p + q) ≫
          (Pi.π (fun j ↦ ((integralOperationsTensorTowerFunctor l E T).obj
            (P,Q)).obj (op j)) n).f (p + q)).val.app U)
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology T)
              (completedIntegralCommRingSheafUnrestricted l E T) P Q p q (p+q) rfl U x y) =
          integralOperationsTotalTensorSection l E T n P Q p q U
            (unrestrictedIntegralTensorSection l E T n (P.X p) U 1 x)
            (unrestrictedIntegralTensorSection l E T n (Q.X q) U 1 y)) ∧
      ∀ (P Q : CochainComplex (integralTowerModules l E T) ℤ) (i : ℤ),
        (eta.app (P,Q)).f i ≫
          (CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism
              (K := fun j ↦ ((integralOperationsTensorTowerFunctor l E T).obj
                (P,Q)).obj (op j))
              (integralOperationsTowerStep
                ((integralOperationsTensorTowerFunctor l E T).obj (P,Q))))).v
                  i (i - 1) (by omega) = 0

/-- The ordinary-to-completed tensor map is the strict quotient augmentation.
Its product component is fixed on all pure total tensors, and its second cone
component is zero. This specifies the full Roos map before localization.
Source: rational purity proof Step 1, completed tensor convention
(blueprint: def-pur-canonical-purity-source-transports).
Proof: send x tensor y to the tensor of their images in each positive quotient.
Balanced tensors and total-summand injections extend this to a chain map to the
product tower. Compatibility with quotient transitions annihilates 1-s.
The mapping-cocone lift with second component zero exists and is unique.
The generator equations and zero second component prove naturality and uniqueness. -/
theorem tensorAugmentation_existsUnique (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    ∃! eta : ordinaryTotal l E T ⟶ integralOperationsTensorComplexFunctor l E T,
      TensorAugmentationNormalized l E T eta := by
  sorry
```

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.PuritySourceTransports` | T3 | Same proposition after unfolding the named predicate; explicit unchanged type for its selected augmentation. |
| `Sheaf.Paper.RationalScalarComparisonData` | P3 | Uses the selected augmentation, whose elaborated type and value are unchanged. No adaptation. |

Other importers use the same constant. The library search finds no external
use of `tensorAugmentation_existsUnique` itself. The node statement is
unchanged because this is only a definitional presentation of its prescribed
normalization, not a different mathematical condition.

## Status

landed 20261025T164341-L-1002274 2026-10-25 (merge of deliver/T3/Sheaf.Paper.PuritySourceTransports)
