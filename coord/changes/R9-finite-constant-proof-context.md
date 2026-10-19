# AlgebraicGeometry.Etale.isIso_finiteConstantProjectionMap

## Reason

The preflight reports a proof-context command change in the item module. The proof
adds a general-coefficient private tensor-bound helper. Its local monoidal instance
avoids comparing expensive concrete module-sheaf monoidal structures during kernel
checking. The instance attribute is scoped to this one private theorem by `in`.
The module also opens `CategoryTheory.MonoidalCategory` to state this private helper.
Neither command exports an instance, notation, or declaration to consumers. All existing
public signatures, public imports, and the canonical map definition are identical.
No public definition changes and no target meaning changes.

## Old

The private helper did not exist. The context commands were:

```lean
universe u

open CategoryTheory CategoryTheory.Limits
```

## New

```lean
universe u u'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
```

The following proved private helper was added inside `AlgebraicGeometry.Etale`:

```lean
attribute [local instance] Sheaf.monoidalCategory in
private theorem isLE_derivedTensor_obj
    (B : Type u') [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (Z : Scheme.{u})
    (U V : DerivedCategory (Sheaf Z.smallEtaleTopology B)) (b c : ℤ)
    [U.IsLE b] [V.IsLE c] :
    (((derivedTensor B Z).obj U).obj V).IsLE (b + c) :=
  _root_.DerivedCategory.isLE_tensor U V b c
```

## Users

The private helper has no external consumers. The existing public declarations are
unchanged; every downstream statement therefore keeps the same meaning and no adaptation
is required. The direct importers and declaration consumers are recorded below.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula` | R9 | Private helper used only in the new proof. |
| `Sheaf.Paper.DirectImageTorAmplitude` | unmodified | Existing map and theorem applications unchanged. |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | unmodified | Public interface unchanged. |
| `Sheaf.Paper.AdicExceptionalProjection` | unmodified | Public interface unchanged. |
| `Sheaf.Paper.FiniteCoefficientDirectImage` | unmodified | Public interface unchanged. |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | unmodified | Public interface unchanged. |
| `Sheaf.Paper.FiniteStageDirectImageTorAmplitude` | unmodified | Public interface unchanged. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unmodified | Public interface unchanged. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | unmodified | Public interface unchanged. |
| `Sheaf.Paper.SfLocalizationAllStages` | unmodified | Public interface unchanged. |
| `Sheaf.Paper.EtaleGeometricBiduality` | unmodified | Public interface unchanged. |

No module held by another group is changed or adapted.

## Status

landed 20261019T112522-L-3949709 2026-10-19 (merge of deliver/R9/Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula)
