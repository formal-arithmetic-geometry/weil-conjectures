# Completed integral finite-tower coefficient transport: new lower declarations

## Reason

Separate the ordinary normalized finite coefficient comparison from strict derived
limit transport, and assemble the assigned theorem without changing its interface.
Only new Sheaf modules and the assigned item are involved. No existing declaration
signature, definition, instance, attribute or public import is changed.

## Old

These two declarations did not exist. The assigned theorem signature remains verbatim.

## New

```lean
theorem finiteIntegral_coefficientComparison
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ e : ∀ n : ℕ, finiteIntegral l E g n ≅ finiteCompleted l E g n,
      ∀ n : ℕ, FiniteNormalization l E g n (e n)
```

```lean
theorem strictIntegral_coefficientTowerTransport
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g)
    (e : ∀ n : ℕ, finiteIntegral l E g n ≅ finiteCompleted l E g n)
    (he : ∀ n : ℕ, FiniteNormalization l E g n (e n))
    (a : pbcActualStrictCompletedPull (pbcIntegralDatum l E) g ≅
      pbcActualCompletedPull g (pbcIntegralDatum l E))
    (ha : ∀ K : PbcCompletedDerived Y (pbcIntegralDatum l E),
      (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K ≫ a.hom.app K =
        (pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).app K) :
    ∃ b : pbcActualStrictCompletedPull (pbcIntegralDatum l E) g ⋙ derived l E X ≅
        finiteTowerLimit l E g C,
      (∀ (P : CochainComplex
          (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
        (hP : integralOperationsGoodComplex.{u, u} l E Y ((complexes l E Y).obj P))
        (n : ℕ),
        b.hom.app (DerivedCategory.Q.obj P) ≫ finiteTowerLimitProjection l E g C P n ≫
            DerivedCategory.Q.map ((finiteComplexComparison l E g n (e n)).app P) =
          (derived l E X).map
            ((completedReductionLimitProjection (pbcIntegralDatum l E) (X := X) n).app
              ((completedTowerPullback g (pbcIntegralDatum l E)).obj
                ((completedReductionTower Y (pbcIntegralDatum l E)).obj
                  (DerivedCategory.Q.obj P))) ≫
              (completedReductionFiniteEvaluation g (pbcIntegralDatum l E) n).hom.app
                (DerivedCategory.Q.obj P)) ≫ finiteComputation l E g P n) ∧
      NatTrans.CommShift (Functor.isoWhiskerRight a.symm (derived l E X) ≪≫ b).hom ℤ
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedIntegralFiniteTowerTransport | J8 | Proof uses both new declarations. |
| Sheaf.Paper.FiniteIntegralCoefficientComparison | new, J8 | States the ordinary comparison. |
| Sheaf.Paper.StrictIntegralCoefficientTowerTransport | new, J8 | States strict transport with finite maps as inputs. |

The new declarations have no existing consumers; no forced adaptation is needed.
Existing consumers of the assigned module retain all original public signatures.
The new statements appear only in theorem proofs; target definitions are unchanged.

## Status

landed 20261028T072423-L-1945101 2026-10-28 (merge of deliver/J8/Sheaf.Paper.CompletedIntegralFiniteTowerTransport)
