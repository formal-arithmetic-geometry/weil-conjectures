# AlgebraicGeometry.Etale.etaleTensorRaw

## Reason

Complete the existing auxiliary hole without changing its statement. Direct concrete
reflexivity exceeds the kernel limit. Prove the identity first for an abstract coefficient
category, then specialize to the sheaf category. The helper module is unclaimed; S1 holds
Sheaf.Paper.DualityPairing. No source-library declaration is changed.

## Old

```lean
theorem etaleTensorRaw
    (B : Type c) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) : derivedTensor B X =
      @curriedTensor _ _ (DerivedMonoidal.instMonoidalCategory _root_.DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology B) (.up ℤ))) := by
  sorry

```

## New

```lean
theorem etaleTensorRaw
    (B : Type c) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) : derivedTensor B X =
      @curriedTensor _ _ (DerivedMonoidal.instMonoidalCategory _root_.DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology B) (.up ℤ))) := by
  exact nativeTensorRaw (Sheaf X.smallEtaleTopology B)

```

The private, completely proved nativeTensorRaw supplies the specialization. The public
signature and all definitions are unchanged. This proof repair does not reopen target
statement review.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DualityPairing | S1 | Uses the same equality, now completely proved. |
| Sheaf.Paper.DualityPairingHelpers | unclaimed | Existing theorem proof filled; private helper added. |

Indirect users reported by downstream.py retain their existing interfaces and need
no adaptation:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DeltaProperPushforward | claimed | Imported interface unchanged. |
| Sheaf.Paper.DeltaRestriction | unclaimed | Imported interface unchanged. |
| Sheaf.Paper.EtaleGeometricBiduality | unclaimed | Imported interface unchanged. |
| Sheaf.Paper.BoundaryAlphaNormalization | unclaimed | Imported interface unchanged. |

## Status

landed 20261020T230831-L-618552 2026-10-20 (merge of deliver/S1/Sheaf.Paper.DualityPairing)
