# AlgebraicGeometry.Scheme.proEtale_torInterval_local_detection

## Reason

P4 proves the assigned theorem with private proof helpers and proof-only imports.
Preflight classifies the added lexical `open scoped ZeroObject` and elaboration
options as commands potentially changing what importers see, and requires this record.
The scope permits the zero sheaf notation in the cover proof; the options permit
categorical instance synthesis and the existing scalar-transport comparison.
No existing declaration signature, definition, attribute, or public import changes.
The additional helper definition constructs a natural isomorphism explicitly; it
contains no postponed proof or chosen mathematical object.

## Old

The original command block is:

```lean
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme
```

The original theorem signature, verbatim, is:

```lean
theorem proEtale_torInterval_local_detection
    (X : Scheme.{u}) (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (K : DerivedCategory (proEtaleRingModules X A)) (c d : ℤ) (_hcd : c ≤ d) :
    (∀ (𝒱 : X.Cover.{u + 1} (Scheme.precoverage @WeaklyEtale))
      (_ : QuasiCompactCover 𝒱.toPreZeroHypercover),
      (∀ t : 𝒱.I₀,
        ∀ (M : proEtaleRingModules (𝒱.X t)
            ((proEtaleSheafInverseImage (𝒱.f t) CommRingCat.{u + 1}).obj A))
          (q : ℤ), q < c ∨ d < q →
          IsZero ((DerivedCategory.homologyFunctor _ q).obj
            ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology (𝒱.X t))
              ((proEtaleSheafInverseImage (𝒱.f t) CommRingCat.{u + 1}).obj A)).obj
              (((proEtaleRingDerivedPullback (𝒱.f t) A _ (Iso.refl _)).obj K),
                (DerivedCategory.singleFunctor _ 0).obj M)))) →
      ∀ (M : proEtaleRingModules X A) (q : ℤ), q < c ∨ d < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X) A).obj
            (K, (DerivedCategory.singleFunctor _ 0).obj M)))) ∧
    (∀ (Z U : Scheme.{u}) (i : Z ⟶ X) (j : U ⟶ X)
      (_ : IsClosedImmersion i) (_ : IsOpenImmersion j) (_ : QuasiCompact j),
      Set.range j = (Set.range i)ᶜ →
      (∀ (M : proEtaleRingModules Z
          ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A))
        (q : ℤ), q < c ∨ d < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology Z)
            ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)).obj
            (((proEtaleRingDerivedPullback i A _ (Iso.refl _)).obj K),
              (DerivedCategory.singleFunctor _ 0).obj M)))) →
      (∀ (M : proEtaleRingModules U
          ((proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj A))
        (q : ℤ), q < c ∨ d < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology U)
            ((proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj A)).obj
            (((proEtaleRingDerivedPullback j A _ (Iso.refl _)).obj K),
              (DerivedCategory.singleFunctor _ 0).obj M)))) →
      ∀ (M : proEtaleRingModules X A) (q : ℤ), q < c ∨ d < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X) A).obj
            (K, (DerivedCategory.singleFunctor _ 0).obj M))))
```

## New

The command block is:

```lean
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
```

The theorem signature is identical to the Old signature above. Its proof now uses
exact pullback, the resolving-class tensor presentation, canonical tensor pullback,
and covering/open-closed zero detection. All additional declarations are private.
The changed commands only affect elaboration in this module. They do not add
notation declarations, instances, or attributes for consumers.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleTorIntervalLocalDetection
--uses proEtale_torInterval_local_detection` reports zero downstream modules and
one declaration-name user, the item itself.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleTorIntervalLocalDetection | P4 | Original theorem proved; signature unchanged; private helpers and lexical proof commands added. |

No target statement or definition used by a target changes. No consumer adaptation
is required. The DAG attachment is retained and its proof route is updated.

## Status

landed 20261021T111408-L-104706 2026-10-21 (merge of deliver/P4/Sheaf.AlgebraicGeometry.ProEtaleTorIntervalLocalDetection)
