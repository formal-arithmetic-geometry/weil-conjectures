/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.Functor.CurryComparison
public import WeilConjectures.WeilSheaf.Native.NativePullTensor
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationDerivedTensor
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalQNormalization
public import WeilConjectures.CategoryTheory.Native.NativeTotalComparisonSummands
public import WeilConjectures.WeilSheaf.Native.NativePullKFlat

/-!
# The condensed realization is compatible with the pullback–tensor comparisons

For a morphism `g : Z ⟶ Y` of `k₀`-schemes, the derived condensed realization `N` carries the
native pullback–tensor comparison `g^*(A ⊗ B) ≅ g^*A ⊗ g^*B`
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTensor`) to the comparison
`Lḡ^*(K ⊗ᴸ L) ⟶ Lḡ^*K ⊗ᴸ Lḡ^*L` of condensed `ℚ̲̄_ℓ`-modules on the geometric fibres
(`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor`), up to the tensor
comparisons `AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationTensor` and the pullback
comparison `AlgebraicGeometry.ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso`:
this is `CategoryTheory.Adjunction.ComparisonCompatible`, the hypothesis of
`CategoryTheory.Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry.ProEtaleWeilSheaf

-- Use Mathlib's Grothendieck instance on module categories, as `nativePullTensor` does, so that
-- the native K-flatness statements agree syntactically.
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The native derived tensor product of pro-étale Weil complexes, curried. -/
noncomputable abbrev nativeCurriedTensor (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] :=
  Functor.curry.obj (nativeDerivedTensor k₀ l X)

/-- The condensed realization commutes with the derived tensor products, in curried form. -/
noncomputable abbrev condensedRealizationCurriedTensor (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] :=
  Functor.curryCompIsoOfIso' (condensedRealizationTensor k₀ l X)

variable {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- The native pullback–tensor comparison `g^*(A ⊗ B) ⟶ g^*A ⊗ g^*B`, in curried form. -/
noncomputable abbrev nativeCurriedPullTensor :=
  (Functor.curryCompIsoOfIso (nativePullTensor k₀ l g)).hom

/-- **The condensed realization of the sheaf-level pullback–tensor comparison** (input). For
pro-étale Weil sheaves `M`, `N` on `Y`, the condensed realization of the comparison
`g^*(M ⊗ N) ≅ g^* M ⊗ g^* N` (`nativePullSheafTensor`), followed by the tensor comparison
`condensedRealizationSheafTensorIso` on `Z`, is the comparison obtained from the tensor comparison
on `Y`, the comonoidal structure of the pullback `ḡ^*` of condensed `ℚ̲̄_ℓ`-modules and the
pullback comparison `condensedRealizationUpperStarIso : N_Y ⋙ ḡ^* ≅ g^* ⋙ N_Z`.

Forgetting the Weil structures, this is a statement about `ℓ`-adic sheaves on the geometric
fibres: the pullback compatibility `ḡ^* ⋙ E_Z ≅ E_Y ⋙ ḡ^*` of the condensed model
`E = adicSheafEquivCondensedMod` (`AlgebraicGeometry.ProEtale.adicUpperStarCompCondensedModIso`,
the conjugate of the pushforward compatibility) is a monoidal natural isomorphism, for the
pullback–tensor comparison `AlgebraicGeometry.ProEtale.adicUpperStarTensorLeftIso` of `ℓ`-adic
sheaves, the monoidal comparison `AlgebraicGeometry.ProEtale.adicSheafEquivCondensedModTensorIso`
of `E` and the strong monoidal structure of the pullback of condensed module objects. It is the
componentwise form of `condensedRealizationUpperStarIso_tensor`
(`WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationPullTotalTensor`), and is not
proved here. -/
theorem tensorComparisonCompatible_condensedRealizationUpperStarIso :
    TensorComparisonCompatible (condensedRealizationUpperStarIso k₀ l g)
      (nativePullSheafTensor k₀ l g) (condensedRealizationSheafTensorIso k₀ l Y)
      (condensedRealizationSheafTensorIso k₀ l Z) :=
  sorry

set_option maxHeartbeats 1000000 in
-- the descent is instantiated at the concrete realization and tensor functors
/-- **Compatibility of the condensed realization with a restriction–tensor comparison.** Let
`R` be an exact functor of pro-étale Weil sheaves from `Y` to `Z` preserving native K-flatness,
`f : Z̄ ⟶ Ȳ` a morphism of the geometric fibres and `a : N_Y ⋙ f^* ≅ R ⋙ N_Z` an isomorphism with
the condensed realizations. Let `r : R (M ⊗ N) ≅ R M ⊗ R N` be a sheaf-level comparison with
totalization `t`. If `r` is carried by the condensed realization to the comonoidal structure of
`f^*` (hypothesis `hS`), then the derived comparison `nativeRestrictionDerivedTensor R hR t` is
carried by the derived condensed realization to the comparison
`Lf^*(K ⊗ᴸ L) ⟶ Lf^* K ⊗ᴸ Lf^* L`, up to `condensedRealizationTensor` and the square induced by
`a`. All four comparisons are normalized on K-flat representatives by totalized sheaf-level
comparisons (`CategoryTheory.comparisonCompatible_of_totalComparison`), which are compatible
summand by summand (`CategoryTheory.totalComparison_compatible_of_sheaf`). -/
theorem comparisonCompatible_nativeRestrictionDerivedTensor
    (R : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l Z) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] [R.IsLeftAdjoint]
    (hR : ∀ T, NativeIsKFlat k₀ l Y T →
      NativeIsKFlat k₀ l Z ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (r : nativeOpenSheafTensor k₀ l Y ⋙ R ≅ R.prod R ⋙ nativeOpenSheafTensor k₀ l Z)
    (t : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (nativeTensorTotal k₀ l Z))
    (ht : NativeRestrictionDescentProof.RestrictionTotalSummands R (nativeOpenSheafTensor k₀ l Z)
      (nativeOpenSheafTensor k₀ l Y) (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
      (nativeOpenTensorInsertion k₀ l Z) (nativeOpenTensorInsertion k₀ l Y) r t)
    (f : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (a : condensedRealization k₀ l Y ⋙
        ProEtale.CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f ≅
      R ⋙ condensedRealization k₀ l Z)
    (hS : TensorComparisonCompatible a r (condensedRealizationSheafTensorIso k₀ l Y)
      (condensedRealizationSheafTensorIso k₀ l Z)) :
    Adjunction.ComparisonCompatible (Functor.leftDerivedFunctorSquareIso a)
      (Functor.curryCompIsoOfIso (nativeRestrictionDerivedTensor k₀ l R hR t)).hom
      (ProEtale.CondensedRing.leftDerivedUpperStarTensor (Profinite.padicAlgClRingObj l) f)
      (condensedRealizationCurriedTensor k₀ l Z) (condensedRealizationCurriedTensor k₀ l Y) := by
  refine comparisonCompatible_of_totalComparison (TC₁ := ?TC₁) (TC₂ := ?TC₂) (TD₁ := ?TD₁)
    (TD₂ := ?TD₂) (fC₁ := ?fC₁) (fC₂ := ?fC₂) (fD₁ := ?fD₁) (fD₂ := ?fD₂) (hF := ?hF)
    (hN₁ := ?hN₁) (hN₂ := ?hN₂) (mC₁ := ?mC₁) (mC₂ := ?mC₂) (mD₁ := ?mD₁) (mD₂ := ?mD₂)
    (tF := ?tF) (tN₁ := ?tN₁) (tN₂ := ?tN₂) a _
    ?hF' ?tF' _ ?hmD ?hφ ?hm₁ ?hm₂ ?hφ' ?H ?hess
  case hφ => exact nativeRestrictionDerivedTensor_normalization k₀ l R hR t
  case hm₁ => exact condensedRealizationTensor_normalization k₀ l Y
  case hm₂ => exact condensedRealizationTensor_normalization k₀ l Z
  case hmD => exact condensedTensorModel_naturality k₀ l Z
  case hF' =>
    exact fun T hT ↦ (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (ProEtale.CondensedRing.kFlat_upperStar_mapHomologicalComplex_obj _ _
        ((HomotopyCategory.kFlat_quotient_obj_iff _).1 hT))
  case hφ' =>
    intro P T hP hT
    have h := ProEtale.CondensedRing.leftDerivedUpperStarTensor_app_app_Q_obj
      (Profinite.padicAlgClRingObj l) f P T
    simp only [Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map,
      Category.assoc] at h ⊢
    convert h using 3
    all_goals rfl
  case H =>
    exact fun P T _ _ ↦ totalComparison_compatible_of_sheaf a r
      (condensedRealizationSheafTensorIso k₀ l Y) (condensedRealizationSheafTensorIso k₀ l Z) t
      (condensedRealizationTotalTensorIso k₀ l Y) (condensedRealizationTotalTensorIso k₀ l Z) ht
      (condensedRealizationTotalTensorIso_summand k₀ l Y)
      (condensedRealizationTotalTensorIso_summand k₀ l Z) hS P T
  case hess =>
    intro x
    have := native_open_tensor_full_kflat_localization k₀ l Y
    have := Localization.essSurj
      (ObjectProperty.ι (NativeIsKFlat k₀ l Y) ⋙ DerivedCategory.Q)
      ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage
        (ObjectProperty.ι (NativeIsKFlat k₀ l Y)))
    let L := ObjectProperty.ι (NativeIsKFlat k₀ l Y) ⋙ DerivedCategory.Q
    exact ⟨(L.objPreimage x).obj, (L.objPreimage x).property, ⟨(L.objObjPreimageIso x).symm⟩⟩


/-- **Compatibility of the condensed realization with the pullback–tensor comparisons.** The
derived condensed realization carries the native pullback–tensor comparison
`g^*(A ⊗ B) ≅ g^* A ⊗ g^* B` to the comparison `Lḡ^*(K ⊗ᴸ L) ⟶ Lḡ^* K ⊗ᴸ Lḡ^* L` of condensed
`ℚ̲̄_ℓ`-modules, up to the tensor comparisons `condensedRealizationTensor` and the pullback
comparison `derivedCondensedRealizationUpperStarIso`: this is
`comparisonCompatible_nativeRestrictionDerivedTensor` for the pullback `g^*`, given the
sheaf-level compatibility `tensorComparisonCompatible_condensedRealizationUpperStarIso`. -/
theorem comparisonCompatible_derivedCondensedRealization :
    Adjunction.ComparisonCompatible (derivedCondensedRealizationUpperStarIso k₀ l g)
      (nativeCurriedPullTensor k₀ l g)
      (ProEtale.CondensedRing.leftDerivedUpperStarTensor (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (condensedRealizationCurriedTensor k₀ l Z) (condensedRealizationCurriedTensor k₀ l Y) :=
  have : (upperStar k₀ l g).IsLeftAdjoint := (upperStarLowerStarAdjunction k₀ l g).isLeftAdjoint
  comparisonCompatible_nativeRestrictionDerivedTensor k₀ l (upperStar k₀ l g)
    (nativeIsKFlat_mapHomologicalComplex_upperStar_obj k₀ l g) (nativePullSheafTensor k₀ l g)
    (nativePullTotalTensor k₀ l g) (nativePullTotalTensor_summands k₀ l g) _
    (condensedRealizationUpperStarIso k₀ l g)
    (tensorComparisonCompatible_condensedRealizationUpperStarIso k₀ l g)

end AlgebraicGeometry.ProEtaleWeilSheaf
