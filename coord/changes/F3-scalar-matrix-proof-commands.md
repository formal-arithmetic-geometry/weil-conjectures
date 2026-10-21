# AlgebraicGeometry.ProEtale.scalarMatrix_inverseImage proof commands

## Reason

The proof adds private scalar-section and scalar-endomorphism lemmas, local
`omit ... in` commands that avoid unnecessary typeclass assumptions on those
lemmas, and the file-local elaboration option
`set_option backward.isDefEq.respectTransparency.types false`.
A final `#print axioms` command verifies the completed public theorem.
The interface checker conservatively reports these added commands as an
interface change. They introduce no exported instances, attributes, notation
or public declarations. All public signatures, comparison definition bodies,
and public imports remain verbatim. There is no target-definition change and
no statement review to reopen.

## Old

The theorem had the following signature, followed by `:= by sorry`:

```lean
theorem scalarMatrix_inverseImage {m n : ℕ}
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)) :
    (CondensedRing.upperStar Λ h).map (scalarMatrix Λ U A) ≫
        (scalarMatrixFreePullbackIso Λ h n).hom =
      (scalarMatrixFreePullbackIso Λ h m).hom ≫ scalarMatrix Λ V A ∧
    ∃ e : (CondensedRing.upperStar Λ h).obj (cokernel (scalarMatrix Λ U A)) ≅
        cokernel (scalarMatrix Λ V A),
      (CondensedRing.upperStar Λ h).map (cokernel.π (scalarMatrix Λ U A)) ≫ e.hom =
        (scalarMatrixFreePullbackIso Λ h n).hom ≫ cokernel.π (scalarMatrix Λ V A)
```

The source had no additional proof elaboration option, scalar helper lemmas,
`omit ... in` commands, or axiom-print command.

## New

The signature above is preserved verbatim and its proof is complete. The
four new helper theorems `scalarSection_image`, `scalarEndomorphism_image`,
`scalarEndomorphism_naturality`, and `scalarRegular_pullback` are private and
fully proved. The extra commands affect only their elaboration and the local
proof checks. The comparison definitions retain their original bodies.
The existing DAG node records the six-step proof and its reused comparison API.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage | F3 | Private proof helpers and file-local commands; public interface unchanged. |

There are no external Lean importers of this module. No other module is adapted.
The parent DAG node continues to use the same theorem statement.

## Status

landed 20261021T100953-L-4180815 2026-10-21 (merge of deliver/F3/Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage)
