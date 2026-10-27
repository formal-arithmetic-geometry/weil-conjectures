# AlgebraicGeometry.ProEtale.BoundedFlatTensorContinuity.bounded_flat_tensor_continuity

## Reason

The stage-3 static interface classifier requires this record for local proof commands:
namespace openings and local irreducibility attributes are conservatively classified as
interface changes. The public theorem signature, all public definition bodies, and public
imports are unchanged. The `open SheafOfModules in` applies only to this theorem command.
The local attributes prevent elaboration from expanding large chosen coefficient and
comparison constructions; they do not alter definitions or their downstream reducibility.
Both theorem proofs replace their original `sorry`s by complete arguments.

## Old

The public theorem signature, verbatim:

```lean
theorem bounded_flat_tensor_continuity
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hne : p ≠ ℓ)
    {X Y : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [QuasiCompact f.left] [QuasiSeparated f.left]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (P : I ⥤ modules Λ Y.left) (c : Cocone P) (_hc : IsColimit c)
    (_hP : ∀ i : I, exactFunctor _ _
      ((curriedTensor (modules Λ Y.left)).obj (P.obj i)))
    (_hC : exactFunctor _ _ ((curriedTensor (modules Λ Y.left)).obj c.pt))
    (_hfP : ∀ i : I, exactFunctor _ _ ((curriedTensor (modules Λ X.left)).obj
      ((pullback Λ f.left).obj (P.obj i))))
    (_hfC : exactFunctor _ _ ((curriedTensor (modules Λ X.left)).obj
      ((pullback Λ f.left).obj c.pt)))
    (K : DerivedCategory (modules Λ X.left))
    (Kc : CochainComplex (modules Λ X.left) ℤ) (_eK : DerivedCategory.Q.obj Kc ≅ K)
    (a : ℤ) (_hK : ∀ n : ℤ, n < a → IsZero (Kc.X n)) :
    Nonempty (IsColimit ((pullback Λ f.left).mapCocone c)) ∧
    (∀ i : I, ∀ n : ℤ, n < a →
      IsZero (((pulledTensor Λ f.left Kc).obj (P.obj i)).X n)) ∧
    (∀ n : ℤ, n < a → IsZero (((pulledTensor Λ f.left Kc).obj c.pt).X n)) ∧
    Nonempty (IsColimit ((pulledTensor Λ f.left Kc).mapCocone c)) ∧
    (∀ n : ℤ, Nonempty (IsColimit
      ((HomologicalComplex.eval (modules Λ X.left) (ComplexShape.up ℤ) n).mapCocone
        ((pulledTensor Λ f.left Kc).mapCocone c)))) ∧
    (∃ A : CochainComplex (modules Λ Y.left) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ Y.left) A ∧
      (∀ n : ℤ, exactFunctor _ _ ((curriedTensor (modules Λ Y.left)).obj (A.X n))) ∧
      Nonempty (DerivedCategory.Q.obj A ≅ (derivedPushforward Λ f.left).obj K)) ∧
    (∀ (A : CochainComplex (modules Λ Y.left) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ Y.left) A →
      (∀ n : ℤ, exactFunctor _ _ ((curriedTensor (modules Λ Y.left)).obj (A.X n))) →
      ∀ _eA : DerivedCategory.Q.obj A ≅ (derivedPushforward Λ f.left).obj K,
        Nonempty (IsColimit ((tensorWith Λ Y.left A).mapCocone c)) ∧
        IsIso (colimit.desc (P ⋙ tensorWith Λ Y.left A)
          ((tensorWith Λ Y.left A).mapCocone c)) ∧
        RepresentsCocone c (tensorWith Λ Y.left A)
          (derivedTensorWith Λ Y.left ((derivedPushforward Λ f.left).obj K))) ∧
    (∃ (J : CochainComplex (modules Λ X.left) ℤ ⥤
          CochainComplex (modules Λ X.left) ℤ) (η : 𝟭 _ ⟶ J),
      ∀ M, QuasiIso (η.app M) ∧ (J.obj M).IsKInjective) ∧
    (∃ e : DerivedCategory.Q.obj ((pulledTensor Λ f.left Kc).obj c.pt) ≅
          (derivedPulledTensor Λ f.left K).obj c.pt,
      ∃ ei : ∀ i : I,
          DerivedCategory.Q.obj ((pulledTensor Λ f.left Kc).obj (P.obj i)) ≅
            (derivedPulledTensor Λ f.left K).obj (P.obj i),
        (∀ (i j : I) (g : i ⟶ j),
          DerivedCategory.Q.map ((pulledTensor Λ f.left Kc).map (P.map g)) ≫ (ei j).hom =
            (ei i).hom ≫ (derivedPulledTensor Λ f.left K).map (P.map g)) ∧
        (∀ i : I,
          DerivedCategory.Q.map ((pulledTensor Λ f.left Kc).map (c.ι.app i)) ≫ e.hom =
            (ei i).hom ≫ (derivedPulledTensor Λ f.left K).map (c.ι.app i)) ∧
        ∀ (J : CochainComplex (modules Λ X.left) ℤ ⥤
            CochainComplex (modules Λ X.left) ℤ) (η : 𝟭 _ ⟶ J)
          (hJ : ∀ M, QuasiIso (η.app M) ∧ (J.obj M).IsKInjective),
          IsIso (DerivedCategory.Q.map
            (colimit.desc (P ⋙ pulledTensor Λ f.left Kc ⋙ replacedPush Λ f.left J)
              ((replacedPush Λ f.left J).mapCocone
                ((pulledTensor Λ f.left Kc).mapCocone c)))) ∧
          ∀ i : I,
            DerivedCategory.Q.map
                (colimit.ι (P ⋙ pulledTensor Λ f.left Kc ⋙ replacedPush Λ f.left J) i) ≫
              DerivedCategory.Q.map
                (colimit.desc (P ⋙ pulledTensor Λ f.left Kc ⋙ replacedPush Λ f.left J)
                  ((replacedPush Λ f.left J).mapCocone
                    ((pulledTensor Λ f.left Kc).mapCocone c))) ≫
              (replacementComparison Λ f.left J η hJ
                ((pulledTensor Λ f.left Kc).obj c.pt)).hom ≫
              (derivedPushforward Λ f.left).map e.hom =
            (replacementComparison Λ f.left J η hJ
                ((pulledTensor Λ f.left Kc).obj (P.obj i))).hom ≫
              (derivedPushforward Λ f.left).map (ei i).hom ≫
              (derivedPushforward Λ f.left).map
                ((derivedPulledTensor Λ f.left K).map (c.ι.app i)))
```

There were no local irreducibility commands in the item. The theorem had no local
`open SheafOfModules in` prefix and its proof was `by sorry`.

## New

The public theorem signature is exactly the same:

```lean
theorem bounded_flat_tensor_continuity
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hne : p ≠ ℓ)
    {X Y : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [QuasiCompact f.left] [QuasiSeparated f.left]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (P : I ⥤ modules Λ Y.left) (c : Cocone P) (_hc : IsColimit c)
    (_hP : ∀ i : I, exactFunctor _ _
      ((curriedTensor (modules Λ Y.left)).obj (P.obj i)))
    (_hC : exactFunctor _ _ ((curriedTensor (modules Λ Y.left)).obj c.pt))
    (_hfP : ∀ i : I, exactFunctor _ _ ((curriedTensor (modules Λ X.left)).obj
      ((pullback Λ f.left).obj (P.obj i))))
    (_hfC : exactFunctor _ _ ((curriedTensor (modules Λ X.left)).obj
      ((pullback Λ f.left).obj c.pt)))
    (K : DerivedCategory (modules Λ X.left))
    (Kc : CochainComplex (modules Λ X.left) ℤ) (_eK : DerivedCategory.Q.obj Kc ≅ K)
    (a : ℤ) (_hK : ∀ n : ℤ, n < a → IsZero (Kc.X n)) :
    Nonempty (IsColimit ((pullback Λ f.left).mapCocone c)) ∧
    (∀ i : I, ∀ n : ℤ, n < a →
      IsZero (((pulledTensor Λ f.left Kc).obj (P.obj i)).X n)) ∧
    (∀ n : ℤ, n < a → IsZero (((pulledTensor Λ f.left Kc).obj c.pt).X n)) ∧
    Nonempty (IsColimit ((pulledTensor Λ f.left Kc).mapCocone c)) ∧
    (∀ n : ℤ, Nonempty (IsColimit
      ((HomologicalComplex.eval (modules Λ X.left) (ComplexShape.up ℤ) n).mapCocone
        ((pulledTensor Λ f.left Kc).mapCocone c)))) ∧
    (∃ A : CochainComplex (modules Λ Y.left) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ Y.left) A ∧
      (∀ n : ℤ, exactFunctor _ _ ((curriedTensor (modules Λ Y.left)).obj (A.X n))) ∧
      Nonempty (DerivedCategory.Q.obj A ≅ (derivedPushforward Λ f.left).obj K)) ∧
    (∀ (A : CochainComplex (modules Λ Y.left) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ Y.left) A →
      (∀ n : ℤ, exactFunctor _ _ ((curriedTensor (modules Λ Y.left)).obj (A.X n))) →
      ∀ _eA : DerivedCategory.Q.obj A ≅ (derivedPushforward Λ f.left).obj K,
        Nonempty (IsColimit ((tensorWith Λ Y.left A).mapCocone c)) ∧
        IsIso (colimit.desc (P ⋙ tensorWith Λ Y.left A)
          ((tensorWith Λ Y.left A).mapCocone c)) ∧
        RepresentsCocone c (tensorWith Λ Y.left A)
          (derivedTensorWith Λ Y.left ((derivedPushforward Λ f.left).obj K))) ∧
    (∃ (J : CochainComplex (modules Λ X.left) ℤ ⥤
          CochainComplex (modules Λ X.left) ℤ) (η : 𝟭 _ ⟶ J),
      ∀ M, QuasiIso (η.app M) ∧ (J.obj M).IsKInjective) ∧
    (∃ e : DerivedCategory.Q.obj ((pulledTensor Λ f.left Kc).obj c.pt) ≅
          (derivedPulledTensor Λ f.left K).obj c.pt,
      ∃ ei : ∀ i : I,
          DerivedCategory.Q.obj ((pulledTensor Λ f.left Kc).obj (P.obj i)) ≅
            (derivedPulledTensor Λ f.left K).obj (P.obj i),
        (∀ (i j : I) (g : i ⟶ j),
          DerivedCategory.Q.map ((pulledTensor Λ f.left Kc).map (P.map g)) ≫ (ei j).hom =
            (ei i).hom ≫ (derivedPulledTensor Λ f.left K).map (P.map g)) ∧
        (∀ i : I,
          DerivedCategory.Q.map ((pulledTensor Λ f.left Kc).map (c.ι.app i)) ≫ e.hom =
            (ei i).hom ≫ (derivedPulledTensor Λ f.left K).map (c.ι.app i)) ∧
        ∀ (J : CochainComplex (modules Λ X.left) ℤ ⥤
            CochainComplex (modules Λ X.left) ℤ) (η : 𝟭 _ ⟶ J)
          (hJ : ∀ M, QuasiIso (η.app M) ∧ (J.obj M).IsKInjective),
          IsIso (DerivedCategory.Q.map
            (colimit.desc (P ⋙ pulledTensor Λ f.left Kc ⋙ replacedPush Λ f.left J)
              ((replacedPush Λ f.left J).mapCocone
                ((pulledTensor Λ f.left Kc).mapCocone c)))) ∧
          ∀ i : I,
            DerivedCategory.Q.map
                (colimit.ι (P ⋙ pulledTensor Λ f.left Kc ⋙ replacedPush Λ f.left J) i) ≫
              DerivedCategory.Q.map
                (colimit.desc (P ⋙ pulledTensor Λ f.left Kc ⋙ replacedPush Λ f.left J)
                  ((replacedPush Λ f.left J).mapCocone
                    ((pulledTensor Λ f.left Kc).mapCocone c))) ≫
              (replacementComparison Λ f.left J η hJ
                ((pulledTensor Λ f.left Kc).obj c.pt)).hom ≫
              (derivedPushforward Λ f.left).map e.hom =
            (replacementComparison Λ f.left J η hJ
                ((pulledTensor Λ f.left Kc).obj (P.obj i))).hom ≫
              (derivedPushforward Λ f.left).map (ei i).hom ≫
              (derivedPushforward Λ f.left).map
                ((derivedPulledTensor Λ f.left K).map (c.ι.app i)))
```

The theorem is locally prefixed with `open SheafOfModules in`. New local proof commands:

```lean
attribute [local irreducible] InternalModuleOperations.coefficientMap
attribute [local irreducible] tensorWith_comparison
attribute [local irreducible] RepresentsCocone
attribute [local irreducible] single_derived_tensor_iso
attribute [local irreducible] derivedPulledTensor_iso
attribute [local irreducible] replacement_computation
attribute [local irreducible] isColimit_map_of_canonical
attribute [local irreducible] isColimit_of_iso_desc
attribute [local irreducible] ring_push_scalar_iso
attribute [local irreducible] replacementComparison replacedPush
  tensorWith derivedTensorWith pulledTensor derivedPulledTensor
attribute [local semireducible] replacedPush tensorWith derivedTensorWith
  pulledTensor derivedPulledTensor
```

The new file option `set_option linter.all false` avoids expensive advisory linting of
the unchanged large theorem signatures and their proofs. It does not affect
proof elaboration, kernel checking, instances, or downstream statements.

All affected constructions retain their original bodies and public signatures. All new
helpers are private and proved. No global attribute is changed.

## Users

`tools/downstream.py Sheaf.Paper.BoundedFlatTensorContinuity --uses
AlgebraicGeometry.ProEtale.BoundedFlatTensorContinuity.bounded_flat_tensor_continuity`
reports zero downstream modules and only the item itself as a textual user. Parent DAG
nodes remain valid and retain their attachments; no mathematical statement changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.BoundedFlatTensorContinuity | B2 | Both theorem holes filled; public signatures unchanged; private proof API added. |

## Status

landed 20261023T230412-L-3423505 2026-10-23 (merge of deliver/B2/Sheaf.Paper.BoundedFlatTensorContinuity)
