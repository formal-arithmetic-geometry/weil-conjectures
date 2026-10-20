# AlgebraicGeometry.Etale.finitePushforward_tensorComparison

## Reason

Close the original proof hole in `Sheaf.AlgebraicGeometry.FinitePushforwardTensorComparison`.
The static interface check also flags added top-level context commands, so this record
makes their scope explicit. The theorem signature, four original definitions and public
imports are verbatim unchanged. Every new helper is private and proved; every attribute
below is local. The new `ProofHelpers` section confines its coefficient-category variables
to private lemmas. No notation, global instance, global reducibility attribute, public
helper or assumption is added.

The local attributes keep elaboration at the ordinary-adjoint and canonical-category APIs
and avoid unfolding large derived constructions. Spelling out the final coefficient
category preserves the statement's instance choices. The final module compiled remotely
without diagnostics in 31.6 seconds. This is a proof and proof-context change, not a change
of mathematical statement or of data. No target meaning changes.

New local attribute commands, verbatim:

```lean
attribute [local irreducible] rightDerivedUpperShriek rightDerivedLowerShriek

attribute [local instance 2000]
  instIsRightAdjointSheafEtaleSmallEtaleTopologyLowerStar
  instIsLeftAdjointSheafEtaleSmallEtaleTopologyUpperStar

attribute [local instance 2000] CommRing.toRing Ring.toSemiring
  _root_.instCategoryDerivedCategory _root_.HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.instCategoryEtale ModuleCat.moduleCategory ObjectProperty.FullSubcategory.category
  Functor.category Category.opposite IsGrothendieckAbelian.hasColimits

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  derivedTensor derivedUpperStarLowerStarAdjunction derivedSquareUpperStarIso
  leftDerivedUpperStarTensorComparison
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
  sheafMonoidalCategory sheafBraidedCategory
  ULift.commRing ZMod.commRing
  ModuleCat.monoidalCategory ModuleCat.instMonoidalPreadditive
```

The new private-helper section's variable context is:

```lean
section ProofHelpers

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]
```

It ends before the projection-formula specialization and the original public theorem.

## Old

```lean
theorem finitePushforward_tensorComparison
    {K : Type u} [Field K]
    {X S' T X' Y I I' J : Scheme.{u}}
    (x : X ⟶ Spec (.of K)) (s : S' ⟶ Spec (.of K))
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
    [QuasiCompact g] [QuasiSeparated g]
    (_sqBase : IsPullback p f' x s) (sqG : IsPullback e h g f')
    (π : I ⟶ X) [IsFinite π] (pI : I' ⟶ I) (π' : I' ⟶ X')
    (hI : J ⟶ I') (ρ : J ⟶ Y)
    (sqPi : IsPullback pI π' π p) (sqRho : IsPullback hI ρ π' h)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : IsUnit (ℓ : K))
    (F : Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :
    IsIso (finiteConstantTensorReduction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sqPi.toCommSq
        (L((f')^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ∧
    IsIso (finiteConstantTensorTargetReduction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
      sqPi.toCommSq sqRho.toCommSq
        (L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ∧
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) h).homEquiv _
      _
        ((((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) h).app
          (L((p)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) I)))).app (L((f')^*[(ModuleCat.{u + 1}
              (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ≫
          ((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) Y).obj
            (L((h)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj (L((p)^*[(ModuleCat.{u + 1}
              (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) I))))).map
            ((derivedSquareUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
              sqG.toCommSq).hom.app
              (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ≫
            L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).map
              ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
                g).counit.app ((_root_.DerivedCategory.singleFunctor _ 0).obj F))))) ≫
      (finiteConstantTensorTargetReduction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
        sqPi.toCommSq sqRho.toCommSq
        (L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) =
      (finiteConstantTensorReduction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sqPi.toCommSq
        (L((f')^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ≫
        R((π')_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).map
          (finitePushforwardUntensoredComparison (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
        sqRho.toCommSq sqG.toCommSq ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ∧
    (IsIso (finitePushforwardUntensoredComparison (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
        sqRho.toCommSq sqG.toCommSq ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) →
      IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
        h).homEquiv _ _
        ((((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) h).app
          (L((p)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) I)))).app (L((f')^*[(ModuleCat.{u + 1}
              (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ≫
          ((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) Y).obj
            (L((h)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj (L((p)^*[(ModuleCat.{u + 1}
              (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) I))))).map
            ((derivedSquareUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
              sqG.toCommSq).hom.app
              (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ≫
            L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).map
              ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
                g).counit.app ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))))) := sorry
```

## New

The signature below is identical; only the proof is filled.

```lean
theorem finitePushforward_tensorComparison
    {K : Type u} [Field K]
    {X S' T X' Y I I' J : Scheme.{u}}
    (x : X ⟶ Spec (.of K)) (s : S' ⟶ Spec (.of K))
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
    [QuasiCompact g] [QuasiSeparated g]
    (_sqBase : IsPullback p f' x s) (sqG : IsPullback e h g f')
    (π : I ⟶ X) [IsFinite π] (pI : I' ⟶ I) (π' : I' ⟶ X')
    (hI : J ⟶ I') (ρ : J ⟶ Y)
    (sqPi : IsPullback pI π' π p) (sqRho : IsPullback hI ρ π' h)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : IsUnit (ℓ : K))
    (F : Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :
    IsIso (finiteConstantTensorReduction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sqPi.toCommSq
        (L((f')^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ∧
    IsIso (finiteConstantTensorTargetReduction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
      sqPi.toCommSq sqRho.toCommSq
        (L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ∧
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) h).homEquiv _
      _
        ((((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) h).app
          (L((p)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) I)))).app (L((f')^*[(ModuleCat.{u + 1}
              (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ≫
          ((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) Y).obj
            (L((h)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj (L((p)^*[(ModuleCat.{u + 1}
              (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) I))))).map
            ((derivedSquareUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
              sqG.toCommSq).hom.app
              (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ≫
            L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).map
              ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
                g).counit.app ((_root_.DerivedCategory.singleFunctor _ 0).obj F))))) ≫
      (finiteConstantTensorTargetReduction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
        sqPi.toCommSq sqRho.toCommSq
        (L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) =
      (finiteConstantTensorReduction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sqPi.toCommSq
        (L((f')^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ≫
        R((π')_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).map
          (finitePushforwardUntensoredComparison (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
        sqRho.toCommSq sqG.toCommSq ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ∧
    (IsIso (finitePushforwardUntensoredComparison (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
        sqRho.toCommSq sqG.toCommSq ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) →
      IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
        h).homEquiv _ _
        ((((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) h).app
          (L((p)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) I)))).app (L((f')^*[(ModuleCat.{u + 1}
              (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ≫
          ((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) Y).obj
            (L((h)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj (L((p)^*[(ModuleCat.{u + 1}
              (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) I))))).map
            ((derivedSquareUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
              sqG.toCommSq).hom.app
              (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ≫
            L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).map
              ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
                g).counit.app ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))))) := by
  -- Spell out the coefficient category to retain the statement's instance choices.
  let F₀ : _root_.DerivedCategory.{u + 1}
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :=
    (_root_.DerivedCategory.singleFunctor _ 0).obj F
  let B : _root_.DerivedCategory.{u + 1}
      (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :=
    L((f')^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
      (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj F₀)
  let V : _root_.DerivedCategory.{u + 1}
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :=
    L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj F₀
  have : IsFinite π' := isFinite_of_isPullback sqPi
  have : IsFinite ρ := isFinite_of_isPullback sqRho
  have hΛ : IsAddTorsion (ULift.{u + 1} (ZMod ℓ)) := isAddTorsion_of_finite
  have hProjπ :
      IsIso (rightDerivedLowerStarProjectionMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) π') :=
    projection_transformation_isIso (ULift.{u + 1} (ZMod ℓ)) hΛ π'
  have hProjρ :
      IsIso (rightDerivedLowerStarProjectionMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) ρ) :=
    projection_transformation_isIso (ULift.{u + 1} (ZMod ℓ)) hΛ ρ
  have hExactπ : PreservesFiniteColimits (π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))] :=
    preservesFiniteColimits_lowerStar_of_isFinite (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) π
  have hExactπ' : PreservesFiniteColimits (π')_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))] :=
    preservesFiniteColimits_lowerStar_of_isFinite (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) π'
  have hExactρ : PreservesFiniteColimits (ρ)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))] :=
    preservesFiniteColimits_lowerStar_of_isFinite (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) ρ
  have hBCπ : IsIso (baseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sqPi.toCommSq) :=
    isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sqPi
  have hBCρ : IsIso (baseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sqRho.toCommSq) :=
    isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sqRho
  have hred := finite_reductions_isIso (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    sqPi.toCommSq sqRho.toCommSq B V
    (hExactπ := hExactπ) (hExactπ' := hExactπ') (hExactρ := hExactρ)
    (hBCπ := hBCπ) (hBCρ := hBCρ) (hProjπ := hProjπ) (hProjρ := hProjρ)
  have hs := hred.1
  have ht := hred.2
  have heq := comparison_commutes (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    sqPi.toCommSq sqRho.toCommSq sqG.toCommSq F₀
  refine ⟨hs, ht, heq, ?_⟩
  intro hβ
  have := hβ
  exact iso_of_reductions R((π')_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]) _ _ _ _ heq
```

## Users

`tools/downstream.py` was run with the module and all five public declaration names.
It found zero downstream Lean modules and only occurrences in the item itself.
The DAG's pending parents retain this node and its original statement. No consumer
requires adaptation, and no module is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.FinitePushforwardTensorComparison` | K5 | Proof closed; private proof context only; public signatures and data unchanged. |

## Status

landed 20261020T211750-L-3498341 2026-10-20 (merge of deliver/K5/Sheaf.AlgebraicGeometry.FinitePushforwardTensorComparison)
