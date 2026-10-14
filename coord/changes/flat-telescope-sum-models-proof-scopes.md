# AlgebraicGeometry.exists_flat_telescope_sum_models: proof-local scopes

## Reason

The static interface checker classifies any changed `variable` or `omit` commands as an
interface change, including section-local commands used only by new private proof helpers.
This delivery introduces three such sections. All end before the existing theorem, all their
helpers are private, and no scoped instance or notation is introduced. There is no change to
any exported declaration, definition, instance, universe, public import, or statement.
This record supplies the conservative check's requested audit trail.

## Old

The module had no helper sections. Its exported declaration's signature is verbatim:

```lean
theorem exists_flat_telescope_sum_models (Y : Scheme.{u})
    (E : ℕ → CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
    (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) :
    ∃ (R : CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (hR : isFlatTelescope Y R)
      (T : ℕ → CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (hT : ∀ n, isFlatTelescope Y (T n))
      (s : ∀ n, (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (T n) ⟶
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R),
      Nonempty ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (∐ E) ≅
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R) ∧
      (∀ n, boundedFlatShiftRepresentative Y
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (T n))) ∧
      Nonempty (IsColimit (Cofan.mk
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R) s))
```

## New

The exported signature above remains verbatim identical. The following scope headers and
closing commands surround only private, fully proved helpers; no variable remains in scope
at the existing theorem. These are the new commands flagged by the checker:

```lean
section PartialSums
variable {C : Type*} [Category C] [Preadditive C]
  [HasBinaryBiproducts C] [HasCountableCoproducts C]
```

The `PartialSums` section also uses `omit [HasBinaryBiproducts C] in` on the private
constant-telescope summand formula, and closes with `end PartialSums`.

```lean
section SplitCone
variable {C : Type*} [Category C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
```

This section closes with `end SplitCone`.

```lean
section HomotopyCoproduct
variable {C : Type*} [Category C] [Preadditive C] [HasCountableCoproducts C]
```

This section closes with `end HomotopyCoproduct`. The declaration-local option
`set_option linter.unusedVariables false in` preserves the original unused existential
proof binder names `hR` and `hT`; it changes only the checking of this theorem.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FlatTelescopeSumModels --uses
exists_flat_telescope_sum_models` identifies the direct theorem caller below. All other
transitive importers see exactly the same public interface. No dependent module needs
adaptation and no target meaning is affected.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FlatTelescopeSumModels | J4 | private proof helper scopes only |
| Sheaf.AlgebraicGeometry.FlatTelescopeSumComparisonIsIso | unclaimed | same theorem signature; no adaptation |

## Status

landed 20261014T092318-L-534072 2026-10-14 (merge of deliver/J4/Sheaf.AlgebraicGeometry.FlatTelescopeSumModels)
