# AlgebraicGeometry.ProEtaleWeilSheaf.NativeOrdinaryTensorModels

## Reason

The H4 audit of the assigned item correctly found that unsigned transposition relative to an arbitrary chosen adjunction and Hom model, even with signed symmetry, does not fix associator normalization. The actual ordinary construction already uses the canonical lax localization tensorator and a signed balanced total isomorphism. Retain precisely that property in the intermediate predicate. The new clause is proved from the explicit existing construction, without a new sorry, in NativeOrdinaryCanonicalTensorRepresentatives. NativeOrdinaryClosedTensorModels is adapted to retain it. Both existing modules are unclaimed.

This is an explicit semantic repair: hypotheses using this intermediate predicate are strengthened, and its existence constructor has the correspondingly stronger conclusion. The supplied normalized ordinaryModel is identified with this witness on K-flat pairs by a proved K-injective cancellation argument. No target signature or adopted source-library declaration is changed. Challenge.lean does not mention this predicate; the semantic review of the affected native closed-model interfaces is reopened. The core DAG node records every current citer and why its use still holds.

## Old

```lean
def NativeOrdinaryTensorModels (Y : Scheme.{u})
    (H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤ DerivedCategory (ProEtale.AdicSheaf l Y))
    (R : NativeHomRepresentatives (ordinaryIhomBifunctor l Y) H)
    (S : CoefficientClosedStructure H) (β : @SymmetricCategory _ _ S.monoidal) : Prop :=
  ∃ model : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
    NativeOrdinaryKFlat l Y P →
      (S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q)),
  ∃ swap : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
    ordinaryTensorTotal l Y P Q ≅ ordinaryTensorTotal l Y Q P,
    NativeAdjunctionNormalization (ordinaryIhomBifunctor l Y)
      (ordinaryTensorBifunctor l Y) (fun P ↦ Mod.ihomAdjunction P)
      H R S (NativeOrdinaryKFlat l Y) model ∧
    NativeOrdinarySignedSwap l Y swap ∧
    (∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (hP : NativeOrdinaryKFlat l Y P) (hQ : NativeOrdinaryKFlat l Y Q),
      (β.toBraidedCategory.braiding (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj P)).hom ≫ (model Q P hQ).hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map (swap P Q).hom)
```

## New

```lean
def NativeOrdinaryTensorModels (Y : Scheme.{u})
    (H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤ DerivedCategory (ProEtale.AdicSheaf l Y))
    (R : NativeHomRepresentatives (ordinaryIhomBifunctor l Y) H)
    (S : CoefficientClosedStructure H) (β : @SymmetricCategory _ _ S.monoidal) : Prop :=
  ∃ model : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
    NativeOrdinaryKFlat l Y P →
      (S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q)),
  ∃ swap : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
    ordinaryTensorTotal l Y P Q ≅ ordinaryTensorTotal l Y Q P,
    NativeAdjunctionNormalization (ordinaryIhomBifunctor l Y)
      (ordinaryTensorBifunctor l Y) (fun P ↦ Mod.ihomAdjunction P)
      H R S (NativeOrdinaryKFlat l Y) model ∧
    NativeOrdinarySignedSwap l Y swap ∧
    (∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (hP : NativeOrdinaryKFlat l Y P) (hQ : NativeOrdinaryKFlat l Y Q),
      (β.toBraidedCategory.braiding (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj P)).hom ≫ (model Q P hQ).hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map (swap P Q).hom) ∧
    (∃ κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
        ordinaryTensorTotal l Y P Q ≅ Q ⊗ P,
      (∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n),
        Mod.tensorπ (Q.X q) (P.X p) ≫
            (HomologicalComplex.ιMapBifunctor P Q (ordinaryTensorBifunctor l Y)
              (.up ℤ) p q n hpq).hom ≫ ((κ P Q).hom.f n).hom =
          (p * q).negOnePow •
            (Mod.tensorObjπ (Q.X q) (P.X p) ≫
              (HomologicalComplex.ιTensorObj Q P q p n hqp).hom)) ∧
      ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (hP : NativeOrdinaryKFlat l Y P) (_hQ : NativeOrdinaryKFlat l Y Q),
        HEq (model P Q hP).hom
          (Functor.LaxMonoidal.μ DerivedCategory.Q Q P ≫
            DerivedCategory.Q.map (κ P Q).inv))
```

## Users

The complete list of modules mentioning the predicate from tools/downstream.py --uses NativeOrdinaryTensorModels is below. In addition, all direct importers of NativeWeilClosedModels are compiled against the changed predicate. Among existing users, only the ordinary existence constructor and this item need source edits. The two new representative modules consume the repaired predicate as well. No module held by another group is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NativeWeilTensorConstraintLifts | unclaimed | Forwards or consumes the predicate; its old clauses stay available, and the added canonical clause is carried through. |
| Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNative | unclaimed | Forwards or consumes the predicate; its old clauses stay available, and the added canonical clause is carried through. |
| Sheaf.Paper.NativeWeilTensorCoherence | unclaimed | Forwards or consumes the predicate; its old clauses stay available, and the added canonical clause is carried through. |
| Sheaf.Paper.NativeWeilTensorGeometry | unclaimed | Forwards or consumes the predicate; its old clauses stay available, and the added canonical clause is carried through. |
| Sheaf.Paper.NativeCoefficientTensorComparison | unclaimed | Forwards or consumes the predicate; its old clauses stay available, and the added canonical clause is carried through. |
| Sheaf.Paper.NativeWeilTensorLift | unclaimed | Forwards or consumes the predicate; its old clauses stay available, and the added canonical clause is carried through. |
| Sheaf.Paper.NativeWeilTensorRingedTransport | unclaimed | Forwards or consumes the predicate; its old clauses stay available, and the added canonical clause is carried through. |
| Sheaf.Paper.NativeWeilClosedModels | unclaimed | Definition strengthened; public import exposes the canonical derived tensor needed in its new clause. |
| Sheaf.Paper.NativeWeilUnitMateIsIso | unclaimed | Forwards or consumes the predicate; its old clauses stay available, and the added canonical clause is carried through. |
| Sheaf.Paper.NativeWeilTensorRingedDerivedSquare | unclaimed | Forwards or consumes the predicate; its old clauses stay available, and the added canonical clause is carried through. |
| Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNativeCoherence | T4 | Signature text unchanged; uses the new clause to normalize the supplied model, then proves all-object descent from two representative lemmas. |
| Sheaf.Paper.NativeGeometricTensorComparison | unclaimed | Forwards or consumes the predicate; its old clauses stay available, and the added canonical clause is carried through. |
| Sheaf.Paper.NativeOrdinaryClosedTensorModels | unclaimed | Existence conclusion gains the canonical clause; proof adapted using the new proved constructor. |
| Sheaf.Paper.NativeWeilTensorAdjoints | unclaimed | Forwards or consumes the predicate; its old clauses stay available, and the added canonical clause is carried through. |
| Sheaf.Paper.NativeWeilTensorRingedDerivedSquareOrdinary | unclaimed | Forwards or consumes the predicate; its old clauses stay available, and the added canonical clause is carried through. |
| Sheaf.Paper.NativeWeilTensorTransport | unclaimed | Forwards or consumes the predicate; its old clauses stay available, and the added canonical clause is carried through. |
| Sheaf.Paper.NativeWeilRingedTensorModel | unclaimed | Forwards or consumes the predicate; its old clauses stay available, and the added canonical clause is carried through. |
| Sheaf.Paper.NativeWeilTensorRingedAssociatorRepresentatives | T4 (new module) | Assumes the repaired predicate and an explicit canonical normalization of the supplied model; isolates associativity on K-flat representatives. |
| Sheaf.Paper.NativeWeilTensorRingedUnitSymmetryRepresentatives | T4 (new module) | Assumes the repaired predicate and explicit canonical normalization; isolates the common unit and signed-symmetry squares on representatives. |

## Status

landed 20261028T055807-L-810289 2026-10-28 (merge of deliver/T4/Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNativeCoherence)
