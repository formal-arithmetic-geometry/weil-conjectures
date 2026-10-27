# AlgebraicGeometry.Etale.ordinary_supported_kummer_chern

## Reason

The component proof uses the supported Chern normalization on the recorded
ordinary derived objects. Use the existing instance proofs for those objects
when elaborating this theorem, to avoid repeatedly comparing expanded category
structures. This is a representation change only: its entire written signature,
proof, imports and declaration attributes are unchanged. The module was unclaimed.
The supporting-module compile passes. Targets using this theorem's structures
are reopened for review that these are the identical library constructions.

## Old

```lean
theorem ordinary_supported_kummer_chern (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) {D : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2)
    (hκ : SupportedKummerBoundary A N hA i hI hT κ) :
    ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T N A hA) 2
      (supportedDerivedUnit A i ≫ supportedExactDerivedMap
        (lowerStar (ModuleCat.{u + 1} A) i) (ordinaryFiniteConstant A D)
        (Scheme.finiteEtaleTateLine T N A hA) κ) =
      supportedKummerChern A N hA i hI hT
```

## New

The exact signature and proof above, with these local attributes before it:

```lean
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000] ordinaryFiniteClass._proof_1 ordinaryFiniteClass._proof_2
  ordinaryFiniteClass._proof_3
```

## Users

The repository scan has no external consumer. This delivery adds the main item
as a proof consumer; its normalization calculation has passed independently.
The same supported divisor Chern class and class realization are used throughout.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.OrdinarySupportedChernNormalization` | unclaimed | Same signature and proof; canonical instance proofs cached. |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula` | F1 | Uses the same supported Chern normalization. |

## Status

landed 20261026T222636-L-676965 2026-10-26 (merge of deliver/F1/Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula)
