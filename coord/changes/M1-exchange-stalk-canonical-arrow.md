# AlgebraicGeometry.Etale.isIso_exchange_stalk_iff_strictLocalCohomology

## Reason

STATEMENT-DISPUTED: the old Lean signature quantifies over an arbitrary morphism α
between the exchange source and target, without identifying it with exchange. The
right side is independent of α. For f = g = id on the spectrum of an algebraically
closed field, q = 0 and the constant integer sheaf, canonical exchange and strict-local
cohomology pullback are invertible, whereas α = 0 has zero map on the nonzero stalk
and is not invertible. This is a false intermediate signature, not a target.
Stacks Project Tag 0EZU, lemma-base-change-f-star-general-stalks, explicitly uses
the canonical exchange. The node's natural-language statement already says this.

The correction adds hα identifying α with that exchange, then proves the corrected
criterion from the two already stated comparison theorems without a new hole. It removes no valid case
of the cited source. Both current calls define α to be this map, so their proofs
supply rfl. No definition or target statement changes. No adopted source-library
module is edited.

## Old

```lean
theorem isIso_exchange_stalk_iff_strictLocalCohomology
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (α : (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      (((g)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus ⋙
        (f)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶
      (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      (((pullback.snd f g)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus ⋙
        (pullback.fst f g)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    (a : Scheme.strictHenselizationRing (x ≫ f) ⟶ Scheme.strictHenselizationRing x)
    (_ : Scheme.strictHenselizationPointEvaluation (x ≫ f) =
      (Scheme.strictHenselizationPointEvaluation x).comp a.hom)
    (ha : Spec.map a ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) =
      Scheme.strictHenselizationStructuralMap x ≫ f) :
    IsIso ((Scheme.pointSmallEtale x).sheafFiber.map α) ↔
      Function.Bijective (cohomologyMap
        (pullback.map (Scheme.strictHenselizationStructuralMap x ≫ f) g
          (Scheme.strictHenselizationStructuralMap (x ≫ f)) g
          (Spec.map a) (𝟙 T) (𝟙 S)
          ((Category.comp_id _).trans ha.symm)
          ((Category.comp_id g).trans (Category.id_comp g).symm))
        ((upperStar AddCommGrpCat.{u + 1}
          (pullback.snd (Scheme.strictHenselizationStructuralMap (x ≫ f)) g)).obj F) q)
```

## New

```lean
theorem isIso_exchange_stalk_iff_strictLocalCohomology
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (α : (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      (((g)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus ⋙
        (f)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶
      (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      (((pullback.snd f g)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus ⋙
        (pullback.fst f g)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    (hα : α = (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (IsPullback.of_hasPullback f g).toCommSq.flip).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    (a : Scheme.strictHenselizationRing (x ≫ f) ⟶ Scheme.strictHenselizationRing x)
    (heval : Scheme.strictHenselizationPointEvaluation (x ≫ f) =
      (Scheme.strictHenselizationPointEvaluation x).comp a.hom)
    (ha : Spec.map a ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) =
      Scheme.strictHenselizationStructuralMap x ≫ f) :
    IsIso ((Scheme.pointSmallEtale x).sheafFiber.map α) ↔
      Function.Bijective (cohomologyMap
        (pullback.map (Scheme.strictHenselizationStructuralMap x ≫ f) g
          (Scheme.strictHenselizationStructuralMap (x ≫ f)) g
          (Spec.map a) (𝟙 T) (𝟙 S)
          ((Category.comp_id _).trans ha.symm)
          ((Category.comp_id g).trans (Category.id_comp g).symm))
        ((upperStar AddCommGrpCat.{u + 1}
          (pullback.snd (Scheme.strictHenselizationStructuralMap (x ≫ f)) g)).obj F) q)
```

## Users

Source audit: tools/downstream.py with --uses found only the item and
Sheaf.AlgebraicGeometry.ExchangeStrictLocalCohomology mentioning the declaration.
The two direct importing modules are listed below. There were no claim lock files
for either module at inspection on 2026-10-25. All transitive consumers retain their
signatures and statements because the parent's statement is verbatim unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ExchangeStrictLocalCohomology | unclaimed | Two proof calls gain the equality argument rfl. Signature and conclusion unchanged. |
| Sheaf.AlgebraicGeometry.IndEtaleQcqsDirectImageBaseChange | unclaimed | Imports the item privately but does not call the declaration. Its stated proof uses canonical exchange, so no adaptation. |

The two DAG parents are lem-weil-pbc-exchange-strict-local-cohomology and
lem-per-ind-etale-qcqs-direct-image-base-change. Both use only canonical exchange,
so neither statement nor planned argument changes. The unit route is untouched.

## Status

landed 20261025T101238-L-3675252 2026-10-25 (merge of deliver/M1/Sheaf.AlgebraicGeometry.ExchangeStrictLocalCohomologyStalk)
