# AlgebraicGeometry.Etale.etaleHomComparison_reversedExact_commShift_core

## Reason

The old core and all-degree signatures allowed arbitrary composite shift structures.
The hypotheses hA and hB constrain sA and sB only; they say nothing about chiPhi
or chiPsi. Twist only chiPhi by the character n ↦ (-1)^n. All old premises stay
unchanged, while the degree-one shift square changes sign. For identity coefficient
change over Q and a nonzero unit comparison, both squares cannot commute. Thus the
arbitrary-shift statement is false.

The source uses the normalized composite shifts. The delivery adds exactly the
hPhi and hPsi component equations that shiftData already supplies and that
IsEtaleHomReversedExact already requires. Its final exactness statement, all
underlying definitions, and all Challenge targets keep their signatures.

## Old

```lean
theorem etaleHomComparison_reversedExact_commShift_core
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M)
    (hv : IsEtaleHomTranspose X φ M v)
    (sA : ((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).CommShift ℤ)
    (sB : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
      ((scalarExtension φ X).obj M)).CommShift ℤ)
    (_chiPhi : (EtaleHomLeft X φ M).CommShift ℤ)
    (_chiPsi : (EtaleHomRight X φ M).CommShift ℤ)
    (hA : EtaleHomShiftNormalization (ModuleCat.{u + 1} A) X M sA)
    (hB : EtaleHomShiftNormalization (ModuleCat.{u + 1} B) X
      ((scalarExtension φ X).obj M) sB)
    (n : ℤ) :
    letI := etaleHomScalarCommShift X φ
    letI := _chiPhi
    letI := _chiPsi
    NatTrans.CommShiftCore v n
```

```lean
theorem etaleHomComparison_reversedExact_commShift
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M)
    (hv : IsEtaleHomTranspose X φ M v)
    (sA : ((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).CommShift ℤ)
    (sB : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
      ((scalarExtension φ X).obj M)).CommShift ℤ)
    (_chiPhi : (EtaleHomLeft X φ M).CommShift ℤ)
    (_chiPsi : (EtaleHomRight X φ M).CommShift ℤ)
    (hA : EtaleHomShiftNormalization (ModuleCat.{u + 1} A) X M sA)
    (hB : EtaleHomShiftNormalization (ModuleCat.{u + 1} B) X
      ((scalarExtension φ X).obj M) sB) :
    letI := etaleHomScalarCommShift X φ
    NatTrans.CommShift v ℤ
```

## New

```lean
theorem etaleHomComparison_reversedExact_commShift_core
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M)
    (hv : IsEtaleHomTranspose X φ M v)
    (sA : ((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).CommShift ℤ)
    (sB : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
      ((scalarExtension φ X).obj M)).CommShift ℤ)
    (_chiPhi : (EtaleHomLeft X φ M).CommShift ℤ)
    (_chiPsi : (EtaleHomRight X φ M).CommShift ℤ)
    (hA : EtaleHomShiftNormalization (ModuleCat.{u + 1} A) X M sA)
    (hB : EtaleHomShiftNormalization (ModuleCat.{u + 1} B) X
      ((scalarExtension φ X).obj M) sB)
    (hPhi :
      letI := etaleHomScalarCommShift X φ
      letI := _chiPhi
      ∀ (K : DerivedCategoryModule A X) (n : ℤ),
        ((EtaleHomLeft X φ M).commShiftIso n).hom.app (op K) =
          (scalarExtension φ X).map ((sA.commShiftIso n).hom.app (op K)) ≫
            ((scalarExtension φ X).commShiftIso n).hom.app
              (((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).obj (op K)))
    (hPsi :
      letI := etaleHomScalarCommShift X φ
      letI := _chiPsi
      ∀ (K : DerivedCategoryModule A X) (n : ℤ),
        ((EtaleHomRight X φ M).commShiftIso n).hom.app (op K) =
          ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
              ((scalarExtension φ X).obj M)).map
            ((((scalarExtension φ X).commShiftIso (-n)).inv.app K).op) ≫
          (sB.commShiftIso n).hom.app (op ((scalarExtension φ X).obj K)))
    (n : ℤ) :
    letI := etaleHomScalarCommShift X φ
    letI := _chiPhi
    letI := _chiPsi
    NatTrans.CommShiftCore v n
```

```lean
theorem etaleHomComparison_reversedExact_commShift
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M)
    (hv : IsEtaleHomTranspose X φ M v)
    (sA : ((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).CommShift ℤ)
    (sB : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
      ((scalarExtension φ X).obj M)).CommShift ℤ)
    (_chiPhi : (EtaleHomLeft X φ M).CommShift ℤ)
    (_chiPsi : (EtaleHomRight X φ M).CommShift ℤ)
    (hA : EtaleHomShiftNormalization (ModuleCat.{u + 1} A) X M sA)
    (hB : EtaleHomShiftNormalization (ModuleCat.{u + 1} B) X
      ((scalarExtension φ X).obj M) sB)
    (hPhi :
      letI := etaleHomScalarCommShift X φ
      letI := _chiPhi
      ∀ (K : DerivedCategoryModule A X) (n : ℤ),
        ((EtaleHomLeft X φ M).commShiftIso n).hom.app (op K) =
          (scalarExtension φ X).map ((sA.commShiftIso n).hom.app (op K)) ≫
            ((scalarExtension φ X).commShiftIso n).hom.app
              (((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).obj (op K)))
    (hPsi :
      letI := etaleHomScalarCommShift X φ
      letI := _chiPsi
      ∀ (K : DerivedCategoryModule A X) (n : ℤ),
        ((EtaleHomRight X φ M).commShiftIso n).hom.app (op K) =
          ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
              ((scalarExtension φ X).obj M)).map
            ((((scalarExtension φ X).commShiftIso (-n)).inv.app K).op) ≫
          (sB.commShiftIso n).hom.app (op ((scalarExtension φ X).obj K))) :
    letI := etaleHomScalarCommShift X φ
    NatTrans.CommShift v ℤ
```

EtaleHomTransposeExact passes hPhi and hPsi from its existing shiftData witnesses
to the all-degree theorem. The all-degree theorem forwards them to the core. The
core is proved by rewriting its two composite-shift components with hPhi and hPsi
and applying the new fixed-degree component lemma
`etaleHomComparison_reversedExact_commShift_component` (still `sorry`; its proof
uses the new `etaleHomTensorComparison_shiftCancellation`, also `sorry`). No
private lemma is added. The unused public ShiftData import is removed from both
intermediate modules; the final exactness module still imports ShiftData directly.
No upstream source module is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.EtaleHomTransposeExactCommShiftCore | C8 | Corrected statement; categorical proof from tensor cancellation. |
| Sheaf.SixFunctors.EtaleHomTransposeExactCommShift | unclaimed | Direct importer and sole caller of core; accepts and forwards hPhi and hPsi. |
| Sheaf.SixFunctors.EtaleHomTransposeExact | unclaimed | Direct importer and sole caller of the all-degree theorem; passes equations it already obtained; signature unchanged. |

The table covers the direct importers and every textual user of the two changed
names found by tools/downstream.py --direct --uses and a whole-library search.
The remaining transitive importers mention neither changed name. Their public
mathematical interfaces are unchanged.

## Status

landed 20261028T072351-L-1937876 2026-10-28 (merge of deliver/C8/Sheaf.SixFunctors.EtaleHomTransposeExactCommShiftCore)
