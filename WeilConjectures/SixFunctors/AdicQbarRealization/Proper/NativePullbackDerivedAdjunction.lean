/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperCoefficientOperations
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement

/-! # The normalized derived adjunction for native coefficient pullback

Source: Stacks Tags 0DVC and 0FND; Bhatt--Scholze Remark 6.8.15.
(blueprint: lem-sf-native-pullback-derived-adjunction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper

/-- An invertible native coefficient map makes ordinary inverse image exact. The
normalized derived counit determines its adjunction to the actual right derived
module direct image, with the representative transpose equation.
Source: Stacks Tags 0DVC and 0FND; Bhatt--Scholze Remark 6.8.15.
(blueprint: lem-sf-native-pullback-derived-adjunction).

Proof: restriction along a coefficient isomorphism is an equivalence. Its scalar
extension left adjoint is also an equivalence, hence exact. Geometric module inverse
image is exact. Thus the ordinary composite is exact, and its termwise localization
is left adjoint to the right derived direct image. Exact scalar extension makes its
universal derived counit invertible on all complexes. The normalization formula then
makes the specified inverse-image counit invertible too. Full faithfulness of
precomposition by the derived localization descends its comparison with the termwise
functor to a natural isomorphism on derived categories. Transport the exact derived
adjunction across that isomorphism. On cochains, the derived-counit identity and the
ordinary adjunction Hom formula give the claimed transpose equation. This uses all
complexes, including unbounded and zero complexes. -/
theorem nativePullbackDerivedAdjunction {X Y : Scheme.{u}} (p : X ⟶ Y)
    {A : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (adicTowerInverseImage p).obj A ⟶ B) [IsIso c]
    [(ContinuousRational.modulePull p c).Additive]
    (a : ContinuousRational.modulePull p c ⊣ ContinuousRational.DirectImage.modulePush p c)
    (δ : DerivedCategory.Q ⋙ ContinuousRational.derivedPull p c ⟶
      (ContinuousRational.modulePull p c).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hδ : ContinuousRational.IsNormalizedPullCounit p c δ) :
    ∃ ad : ContinuousRational.derivedPull p c ⊣ ContinuousRational.DirectImage.derivedPush p c,
      ∀ (P : CochainComplex (pbcModules Y A) ℤ)
        (I : CochainComplex (pbcModules X B) ℤ)
        (t : ((ContinuousRational.modulePull p c).mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
        ad.homEquiv _ _ (δ.app P ≫ DerivedCategory.Q.map t) =
          DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv P I t) ≫
            ContinuousRational.DirectImage.pushUnit p c I := by
  let F := ContinuousRational.modulePull p c
  let G := ContinuousRational.DirectImage.modulePush p c
  let L := ContinuousRational.derivedPull p c
  letI : (pbcRestrict c).IsEquivalence :=
    inferInstanceAs (ProEtale.CondensedRing.ringModuleEquivalenceOfIso X
      ((adicLisseForget X).mapIso (asIso c))).functor.IsEquivalence
  letI : (pbcExtend c).IsEquivalence :=
    (pbcScalarAdjunction c).isEquivalence_left_of_isEquivalence_right
  letI : PreservesFiniteLimits (pbcExtend c) := inferInstance
  letI : PreservesFiniteColimits (pbcExtend c) := inferInstance
  letI : PreservesFiniteLimits (proEtaleModuleInverseImage p A) :=
    proEtaleModuleInverseImage_preservesFiniteLimits p A
  letI : PreservesFiniteLimits F := by
    dsimp only [F, ContinuousRational.modulePull]
    infer_instance
  letI : PreservesColimitsOfSize.{0, 0} F := a.leftAdjoint_preservesColimits
  letI : PreservesFiniteColimits F := inferInstance
  let W := HomotopyCategory.quasiIso (pbcModules X ((adicTowerInverseImage p).obj A)) (.up ℤ)
  have hinv : W.IsInvertedBy ((pbcExtend c).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh) := by
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso W (pbcExtend c).mapDerivedCategoryFactorsh]
    exact MorphismProperty.IsInvertedBy.of_comp W DerivedCategory.Qh
      (Localization.inverts DerivedCategory.Qh W) (pbcExtend c).mapDerivedCategory
  letI := pbcDerivedExtension_universal c
  letI : IsIso (pbcExtensionCounit c) :=
    Functor.isIso_of_isLeftDerivedFunctor_of_inverts (pbcDerivedExtend c)
      (pbcExtensionCounit c) hinv
  obtain ⟨e₀, eC, heC, hpure, hd⟩ := hδ
  have hδiso (P : CochainComplex (pbcModules Y A) ℤ) : IsIso (δ.app P) := by
    rw [hd]
    unfold pbcComplexCounit
    infer_instance
  letI : IsIso δ := NatIso.isIso_of_isIso_app δ
  let γ : DerivedCategory.Q ⋙ L ≅ DerivedCategory.Q ⋙ F.mapDerivedCategory :=
    asIso δ ≪≫ F.mapDerivedCategoryFactors.symm
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (pbcModules Y A) (.up ℤ)) (DerivedCategory (pbcModules X B))
  let e : L ≅ F.mapDerivedCategory := ff.preimageIso γ
  have he (P : CochainComplex (pbcModules Y A) ℤ) :
      e.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P =
        δ.app P := by
    have h := congrArg (fun t ↦ t.app P) (ff.map_preimage γ.hom)
    change e.hom.app (DerivedCategory.Q.obj P) =
      δ.app P ≫ F.mapDerivedCategoryFactors.inv.app P at h
    rw [h, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  let ad := a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft e.symm
  refine ⟨ad, ?_⟩
  intro P I t
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply, ← he P]
  simp only [Iso.symm_hom, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply (a.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc]
  have hρ : ContinuousRational.DirectImage.pushUnit p c I =
      CategoryTheory.UnboundedExactTower.cochainUnit G I := by
    let u := G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I)
    let v := G.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app I)
    let i := (DerivedCategory.quotientCompQhIso _).inv.app
      ((G.mapHomologicalComplex (.up ℤ)).obj I)
    have hi : DerivedCategory.Qh.map
        ((G.mapHomotopyCategoryFactors (.up ℤ)).inv.app I) =
        𝟙 (DerivedCategory.Qh.obj ((G.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj I))) := by
      change DerivedCategory.Qh.map (𝟙 _) = 𝟙 _
      exact DerivedCategory.Qh.map_id _
    exact (congrArg (fun z ↦ i ≫ z) (Category.id_comp (u ≫ v))).symm.trans
      (congrArg (fun z ↦ i ≫ z ≫ u ≫ v) hi).symm
  rw [hρ, CategoryTheory.UnboundedExactTower.cochain_counit]
  have hn := F.mapDerivedCategoryFactors.hom.naturality
    (((a.mapHomologicalComplex (.up ℤ)).homEquiv P I) t)
  change F.mapDerivedCategory.map (DerivedCategory.Q.map _) ≫ _ = _ at hn
  rw [← Category.assoc, hn]
  simp only [CategoryTheory.Functor.comp_map]
  rw [Category.assoc, ← DerivedCategory.Q.map_comp]
  congr 2
  exact ((a.mapHomologicalComplex (.up ℤ)).homEquiv P I).symm_apply_apply t |>.symm

end WeilConjectures.AdicQbarRealization.Proper
