# AlgebraicGeometry.Scheme.isConstructibleSheaf_of_finite_lowerStar_module

## Reason

The eight-clause module assertion transfer needs constructibility reflection for
arbitrary commutative coefficients. Existing finite-pushforward descent specializes
to torsion abelian sheaves and canonical integral coefficients. This new helper isolates
only that coefficient-property step. It does not change an existing definition or
statement. Its complete argument uses finite stratification and direct summands,
rather than an arbitrary quotient closure assertion requiring Noetherian coefficients.

## Old

No declaration of this name exists in the library.

## New

```lean
theorem Scheme.isConstructibleSheaf_of_finite_lowerStar_module
    {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [IsCurve g] [IsFinite f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : Scheme.IsConstructibleSheaf
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)) :
    Scheme.IsConstructibleSheaf F
```

The surrounding parameters are Λ : Type (u + 1) with CommRing Λ.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardModuleAssertions | P2 | Proof-only import; helper used for C4/C5. Existing signature and visibility stay identical. |

The declaration is new, so it has no pre-existing users. There are no forced adaptations
and no changed target definitions.

## Status

landed 20261012T160830-L-2612146 2026-10-12 (merge of deliver/P2/Sheaf.AlgebraicGeometry.Curve.FinitePushforwardModuleAssertions)
