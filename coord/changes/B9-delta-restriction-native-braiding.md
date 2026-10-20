# AlgebraicGeometry.Etale.deltaRestrictionPairingBraiding; AlgebraicGeometry.ProEtale.deltaRestrictionPairingBraiding

## Reason

Construct the prescribed descended Koszul braiding directly instead of choosing it through the ambient pairing existence proposition. The old proposition fixes every component by heterogeneous equality to this same braiding. Reducing the choice predicate at concrete module coefficients made the comparison proofs exceed elaboration limits. Both signatures and all target statements stay identical. This is a construction repair, not a different choice of symmetry. Targets depending on these definitions require renewed semantic review.

## Old

```lean
def deltaRestrictionPairingBraiding
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u})
    (Ω : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (h : AmbientDualityPairing A Y Ω) :
    derivedTensor A Y ≅ (derivedTensor A Y).flip :=
  Classical.choose h

def deltaRestrictionPairingBraiding
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u})
    (Ω : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (h : AmbientDualityPairing A Y Ω) :
    deltaRestrictionNativeTensor A Y ≅
      (deltaRestrictionNativeTensor A Y).flip :=
  Classical.choose h
```

## New

```lean
def deltaRestrictionPairingBraiding
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u})
    (Ω : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (h : AmbientDualityPairing A Y Ω) :
    derivedTensor A Y ≅ (derivedTensor A Y).flip :=
  letI := derivedBraidedCategory A Y
  let _ := h
  BraidedCategory.curriedBraidingNatIso _

def deltaRestrictionPairingBraiding
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u})
    (Ω : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (h : AmbientDualityPairing A Y Ω) :
    deltaRestrictionNativeTensor A Y ≅
      (deltaRestrictionNativeTensor A Y).flip :=
  letI := _root_.DerivedCategory.braidedCategory' (Sheaf (Scheme.ProEt.topology Y) A)
  let _ := h
  BraidedCategory.curriedBraidingNatIso _
```

## Users

`tools/downstream.py Sheaf.Paper.DeltaRestriction --uses deltaRestrictionPairingBraiding` reports four direct uses, all in the item module. The 31 downstream modules have no direct occurrence of the changed identifier. The existing specialized braiding/map/transpose interfaces retain their signatures and the prescribed components. No external module requires a forced adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DeltaRestriction | B9 | Both native braiding constructions repaired; restriction proofs use their prescribed components. |


## Status

landed 20261020T221056-L-4141280 2026-10-20 (merge of deliver/B9/Sheaf.Paper.DeltaRestriction)
