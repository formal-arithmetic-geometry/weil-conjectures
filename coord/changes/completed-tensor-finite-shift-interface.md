# integralCompletedTensorFiniteShiftFormula

## Reason

The delivery first moved this predicate from `Sheaf.SixFunctors.CompletedTensorShiftRight`
to the new module `Sheaf.SixFunctors.CompletedTensorFiniteShift`, so that the finite
tower theorem could state its conclusion with it. That made the statement of
`lem-sf-completed-tensor-shift-right` (through `integralCompletedTensorRightShiftProperty`)
use a declaration owned by `lem-sf-completed-tensor-finite-shift`, a node outside its
`stmt_deps`, and turned the import of the new module into a public import.

Reviewer correction (2026-10-21): the move is withdrawn. The predicate stays in its
original module, owned by its original node, byte for byte. The new theorem
`integralCompletedTensorFiniteShift` writes the same generator equation out in its
own statement, and the item proof unfolds the predicate to use it. The item imports
the new module with a plain `import`.

## Old

Defined in `Sheaf.SixFunctors.CompletedTensorShiftRight`:

```lean
def integralCompletedTensorFiniteShiftFormula (W : AlgebraicGeometry.Scheme.{t})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ)
    (α : (integralOperationsTensorTowerFunctor l E W).obj (P, Q⟦r⟧) ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P, Q) ⋙
        shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r) : Prop :=
  ∀ (n : ℕ) (i j : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X i).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X (j + r)).val.obj U),
    (((α.hom.app (op n)).f (i + j)).val.app U)
      (integralOperationsTotalTensorSection l E W n P (Q⟦r⟧) i j U x y) =
    ((CochainComplex.shiftFunctorObjXIso
      ((integralOperationsTensorLevel l E W n).obj (P, Q))
        r (i + j) (i + (j + r)) (by omega)).inv.val.app U)
      ((r * i).negOnePow •
        integralOperationsTotalTensorSection l E W n P Q i (j + r) U x y)
```

## New

Unchanged: the same declaration, in the same module, recorded by the same node
`lem-sf-completed-tensor-shift-right`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.CompletedTensorShiftRight | J8 | Keeps the predicate; its proof unfolds it to apply the finite tower theorem. |
| Sheaf.SixFunctors.CompletedTensorFiniteShift | J8, new | States the generator equation inline; does not mention the predicate. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Unaffected. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Unaffected. |

## Status

landed 20261020T230756-L-611403 2026-10-20 (merge of deliver/J8/Sheaf.SixFunctors.CompletedTensorShiftRight)
