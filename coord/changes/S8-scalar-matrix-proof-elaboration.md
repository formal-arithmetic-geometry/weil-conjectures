# AlgebraicGeometry.ProEtale.scalarMatrix_inverseImage proof elaboration

## Reason

The complete proof uses four private proved helpers and locally scoped
`omit ... in` and `set_option backward.isDefEq.respectTransparency.types false in`
commands. These commands affect elaboration only. The canonical comparison
definitions, all public signatures, and all public imports are unchanged.
No target definition changes and no consumer adaptation is necessary.

## Old

The module has `set_option autoImplicit false` and no scoped elaboration commands
before its scalar-matrix theorem. The old theorem, verbatim:

```lean
theorem scalarMatrix_inverseImage {m n : ℕ}
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)) :
    (CondensedRing.upperStar Λ h).map (scalarMatrix Λ U A) ≫
        (scalarMatrixFreePullbackIso Λ h n).hom =
      (scalarMatrixFreePullbackIso Λ h m).hom ≫ scalarMatrix Λ V A ∧
    ∃ e : (CondensedRing.upperStar Λ h).obj (cokernel (scalarMatrix Λ U A)) ≅
        cokernel (scalarMatrix Λ V A),
      (CondensedRing.upperStar Λ h).map (cokernel.π (scalarMatrix Λ U A)) ≫ e.hom =
        (scalarMatrixFreePullbackIso Λ h n).hom ≫ cokernel.π (scalarMatrix Λ V A) := by
  sorry
```

## New

Four private proved scalar-section and regular-module helper lemmas precede the
existing theorem, whose proof is complete. The conversion option is scoped to
individual declarations, with unused assumptions omitted from helper declarations.
All exported definitions and statements retain their original text. A final
`#print axioms` command checks the completed theorem; it introduces no declaration.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage | S8 | Private proof helpers and scoped elaboration commands only. |

A source search and `tools/downstream.py --uses` find no current Lean importers
or external uses. The DAG parent continues to use the unchanged theorem.

## Status

landed 20261021T152358-L-1918548 2026-10-21 (merge of deliver/S8/Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage)
