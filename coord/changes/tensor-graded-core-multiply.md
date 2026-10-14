# tensorGradedPresentation_core_multiply

## Reason

Repair return X-f9ba3, E2/E7. The arbitrary-core assertion is false. On the
identity immersion of Spec Q with L = O and B = C = O[T], set p = id and I = 0,
scale b_d and c_d by 2 and the coefficient projections by 1/2. All core fields
hold, while degree-zero multiplication asserts 4 = 2. Require the full
presentation and project its supplied b_multiply field. This is a statement
correction under stages/3-proving-and-pruning.md §3, not a proof of the old claim.
The node records statement_change, its counterexample, and its citer review.
No target statement, definition, or structure changes.

## Old

```lean
theorem tensorGradedPresentation_core_multiply {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible]
    (T : TensorGradedPresentationCore j L) :
    ∀ (U : X.Opens) (a d : ℕ) (s : Γ(L.tensorPow a, U))
      (t : Γ(L.tensorPow d, U)),
      tensorGradedAlgebraSection T.B U ((T.b a).app U s) *
        tensorGradedAlgebraSection T.B U ((T.b d).app U t) =
        tensorGradedAlgebraSection T.B U
          ((T.b (a + d)).app U ((L.tensorPowAddIso a d).inv.app U (tmulSection s t)))
```

## New

```lean
theorem tensorGradedPresentation_core_multiply {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible]
    (T : TensorGradedPresentation j L) :
    ∀ (U : X.Opens) (a d : ℕ) (s : Γ(L.tensorPow a, U))
      (t : Γ(L.tensorPow d, U)),
      tensorGradedAlgebraSection T.B U ((T.b a).app U s) *
        tensorGradedAlgebraSection T.B U ((T.b d).app U t) =
        tensorGradedAlgebraSection T.B U
          ((T.b (a + d)).app U ((L.tensorPowAddIso a d).inv.app U (tmulSection s t)))
```

The proof is `T.b_multiply`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SquareZeroTensorGradedPresentation | N1 (this item) | Its old full-existence proof cited the false assertion. The delivered proof instead constructs the field from A.b_multiply, so no additional adaptation is required. |

The repository-wide Lean name scan and tools/downstream.py --uses find no external
user of this theorem (177 transitive importers; only this module mentions its
name). No downstream signature changes or forced adaptations are necessary.
The sole DAG citer is lem-sc-square-zero-tensor-graded-presentation. Its delivered
proof and proof_deps already remove this theorem and construct the full
presentation using A.b_multiply; holds = true for the revised proof route.
The unit sk-thm-curveestimate realizes neither this auxiliary node nor a step
using it, and its route stays unchanged.

## Status

landed 20261014T050528-L-1685784 2026-10-14 (merge of deliver/N1/Sheaf.AlgebraicGeometry.SquareZeroTensorGradedPresentation)
