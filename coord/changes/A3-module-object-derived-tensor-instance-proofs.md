# AlgebraicGeometry.ProEtale.CondensedRing: derived tensor instance proofs

## Reason

Replace two whole upstream `sorry` bodies by proofs, preserving their exact
signatures and attributes. The interface scanner records instance bodies even
when they are propositions, so this record documents the proof changes.
Neither the comparison morphism nor either counit's construction is changed.
Both instances inhabit propositions, so proof irrelevance preserves every
existing mathematical meaning and every target statement. No target review
is reopened by a change of data or definitions.

The right bifunctor is derived on pairs whose pullbacks are K-flat. The
inverse-image flatness theorem supplies that derivability structure; the
complex tensor isomorphism and the invertible localization tensorator supply
the required counit isomorphisms. The tensor comparison is then invertible by
uniqueness of the left derived bifunctor, applied to the identity.

## Old

```lean
instance isLeftDerivedFunctor₂_upperStarTensor :
    (leftDerivedUpperStarTensorRight Λ f).IsLeftDerivedFunctor₂
      (leftDerivedUpperStarTensorRightCounit Λ f)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  sorry
```

```lean
instance isIso_leftDerivedUpperStarTensor : IsIso (leftDerivedUpperStarTensor Λ f) :=
  sorry
```

## New

```lean
instance isLeftDerivedFunctor₂_upperStarTensor :
    (leftDerivedUpperStarTensorRight Λ f).IsLeftDerivedFunctor₂
      (leftDerivedUpperStarTensorRightCounit Λ f)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
  have hflat : (f)^*⟦Λ⟧.PreservesFlat := by
    let G := (f)^*[Ab.{u + 1}]
    let R := condensedRingObj Λ Y
    let ρ := (asIso (condensedPullbackHom Λ f)).inv
    have h := ProEtale.inverseImageModule_preservesFlat f R (condensedRingObj Λ X) ρ
    let e : (f)^*⟦Λ⟧ ≅ Mod.mapModComap ρ :=
      Functor.isoWhiskerLeft (G.mapMod R)
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))
    exact ⟨fun hM ↦ (ObjectProperty.flat).prop_of_iso (e.symm.app _) (h.flat_obj hM)⟩
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIsoLocalizerMorphism (f)^*⟦Λ⟧.kFlatMap)
    (HomotopyCategory.quasiIsoLocalizerMorphism (f)^*⟦Λ⟧.kFlatMap) _ ?_
  intro A B
  have hμ := Functor.isIso_μNatTrans_Qh_app_app_of_kFlat
    (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A.obj) _ B.property
  have hc : IsIso (upperStarTensorComplexHom Λ f A.obj.as B.obj.as) :=
    isIso_upperStarTensorComplexHom Λ f A.obj.as B.obj.as
  have hα : IsIso (((upperStarTensorCounit Λ f).app A.obj).app B.obj) :=
    IsIso.comp_isIso' hμ (Functor.map_isIso DerivedCategory.Qh
      ((HomotopyCategory.quotient _ _).map
        (upperStarTensorComplexHom Λ f A.obj.as B.obj.as)))
  exact isIso_tensorCounit_app_app DerivedCategory.Qh L((f)^*⟦Λ⟧)
    ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (upperStarTensorTarget Λ f) (f)^*⟦Λ⟧.leftDerivedFunctorCounit
    (upperStarTensorCounit Λ f) A.obj B.obj
```

```lean
instance isIso_leftDerivedUpperStarTensor : IsIso (leftDerivedUpperStarTensor Λ f) := by
  have hleft : (leftDerivedUpperStarTensorLeft Λ f).IsLeftDerivedFunctor₂
      (leftDerivedUpperStarTensorLeftCounit Λ f)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
    exact Functor.isLeftDerivedFunctor₂_leftDerivedDerivedTensor (f)^*⟦Λ⟧
  have h : leftDerivedUpperStarTensor Λ f =
      Functor.leftDerived₂NatTrans (leftDerivedUpperStarTensorRight Λ f)
        (leftDerivedUpperStarTensorRightCounit Λ f)
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
        (leftDerivedUpperStarTensorLeft Λ f) (leftDerivedUpperStarTensorLeftCounit Λ f)
        (𝟙 _) := by
    simp only [Functor.leftDerived₂NatTrans, Category.comp_id, leftDerivedUpperStarTensor]
  rw [h]
  infer_instance
```

## Users

`tools/downstream.py` was run for both instance names. Its direct textual
users are listed below. Downstream instances continue to infer proofs of the
identical propositions; no consumer source requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal | A3 | Two proof bodies filled; all signatures and data unchanged. |

## Status

landed 20261017T112927-L-3881922 2026-10-17 (merge of deliver/A3/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal)
