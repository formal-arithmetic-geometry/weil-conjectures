/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import WeilConjectures.SixFunctors.FrobeniusCohomologyRealization
import WeilConjectures.SixFunctors.FrobeniusCohomologyRealization
import WeilConjectures.SixFunctors.CohomologyRealization.FrobeniusCohomologyComparisonFactors
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonIsomorphism
import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonNatural
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! # Invertibility of the factors of Frobenius transport -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

private instance pointRestrictionIsIso (D : FiniteFieldDatum.{u}) :
    IsIso (frobeniusPointRestriction D) := by
  let j : ProEt.mk (𝟙 (Spec (.of D.k))) ⟶
      (proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj
        (ProEt.mk (𝟙 (Spec (.of D.k)))) :=
    MorphismProperty.Over.homMk (inv (frobeniusPointIso D).hom) (by
      change inv (frobeniusPointIso D).hom ≫ (𝟙 _ ≫ (frobeniusPointIso D).hom) = 𝟙 _ ≫ 𝟙 _
      simp only [Category.id_comp, IsIso.inv_hom_id]) trivial
  have hr : (frobeniusPointRestriction D).left = (frobeniusPointIso D).hom :=
    congrArg (fun f ↦ f.left) ((ProEt.forget (Spec (.of D.k))).map_preimage
      (X := (proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj
        (ProEt.mk (𝟙 (Spec (.of D.k)))))
      (Y := ProEt.mk (𝟙 (Spec (.of D.k)))) (Over.homMk (frobeniusPointIso D).hom))
  refine ⟨⟨j, ?_, ?_⟩⟩
  · apply MorphismProperty.Over.Hom.ext
    change (frobeniusPointRestriction D).left ≫ inv (frobeniusPointIso D).hom = 𝟙 _
    rw [hr]
    exact IsIso.hom_inv_id (frobeniusPointIso D).hom
  · apply MorphismProperty.Over.Hom.ext
    change inv (frobeniusPointIso D).hom ≫ (frobeniusPointRestriction D).left = 𝟙 _
    rw [hr]
    exact IsIso.inv_hom_id (frobeniusPointIso D).hom

private theorem finiteSigmaIsIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (K : CochainComplex
      (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    IsIso (frobeniusPointFiniteSigma D l E n K) := by
  have (i : ℤ) : IsIso ((frobeniusPointFiniteSigma D l E n K).f i) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun x ↦ (frobeniusPointFiniteSigma D l E n K).f i x)
    dsimp only [frobeniusPointFiniteSigma]
    exact (congrArg Function.Bijective
      (eq_of_heq ((frobeniusPointFiniteSigma_existsUnique D l E n K).choose_spec.1 i))).mpr
        (ConcreteCategory.bijective_of_isIso
          ((K.X i).val.presheaf.map (frobeniusPointRestriction D).op))
  exact HomologicalComplex.Hom.isIso_of_components _

private theorem integralSigmaIsIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    IsIso (frobeniusPointIntegralSigma D l E K) := by
  have (i : ℤ) : IsIso ((frobeniusPointIntegralSigma D l E K).f i) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun x ↦ (frobeniusPointIntegralSigma D l E K).f i x)
    dsimp only [frobeniusPointIntegralSigma]
    exact (congrArg Function.Bijective
      (eq_of_heq ((frobeniusPointIntegralSigma_existsUnique D l E K).choose_spec.1 i))).mpr
        (ConcreteCategory.bijective_of_isIso
          ((K.X i).val.presheaf.map (frobeniusPointRestriction D).op))
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Finite ambient point restriction and complete constructible integral restriction are invertible.
Source: Deligne, Weil II (1.1.7); inverse-image restriction in the node's step 2
(blueprint: lem-weil-frobenius-ambient-point-invertibility).
Proof: identify inverse image along the point automorphism with evaluation at the
corresponding object of the pro-etale site. Restriction along that object's isomorphism
has inverse restriction along the inverse. The coefficient comparison is pulled back
from the same constant ring, hence respects scalars. The two inverse equations hold
termwise and survive exact sections and derived localization. For integral systems use
the same inverse at each finite level. Constructibility supplies derived completeness,
so reconstruction identifies the object with the total derived limit of its reductions.
Compatibility with transition maps then gives inverse maps of the Roos realizations. -/
theorem frobeniusAmbientPoint_isIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (∀ (n : ℕ) (N : proEtaleDerivedCategory (Spec (.of D.k))
        (Padic.coefficientExtensionRing l E (n + 1))),
      IsIso (frobeniusPointTransportFinite D l hl E n N)) ∧
    (∀ N : sfIntegralConstructibleCategory l E (Spec (.of D.k)),
      IsIso (frobeniusPointTransportIntegral D l hl E N.obj)) := by
  constructor
  · intro n N
    have : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
      Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    have := finiteSigmaIsIso D l E n (DerivedCategory.Q.objPreimage N)
    have := inverseImageFiniteComparisonComplex_isIso l E (frobeniusPointIso D).hom n
      (DerivedCategory.Q.objPreimage N)
    dsimp only [frobeniusPointTransportFinite, frobeniusPointTransportFiniteComplex,
      inverseImagePullbackComparisonFiniteIntrinsic, inverseImagePullbackComparisonFinite]
    infer_instance
  · intro N
    let g := (frobeniusPointIso D).hom
    let H := inverseImageIntegralDerived l E g
    let T := integralDerivedPullback l E g
    obtain ⟨κ, hk, hres, hθ, _⟩ := inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0}
      l E g (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl)
    obtain ⟨S, hS⟩ := coefficientDerivedSystemEvaluationCalculus l E (Spec (.of D.k))
    obtain ⟨θ, he⟩ := hθ S hS
    have hu : IsIso (S.adjunction.unit.app N.obj) := by
      obtain ⟨R, _⟩ := integralPullbackComparisonRealization l E E (AlgHom.id ℚ_[l] E)
      let U := (R.coefficient E).system (Spec (.of D.k))
      have := (R.coefficient E).complete (Spec (.of D.k)) N
      have hunit := U.adjunction.unit_leftAdjointUniq_hom_app S.adjunction N.obj
      rw [← hunit]
      infer_instance
    have hκ : IsIso (κ.app N.obj) := by
      rw [he N.obj]
      infer_instance
    let K := DerivedCategory.Q.objPreimage N.obj
    let e := DerivedCategory.Q.objObjPreimageIso N.obj
    have hκK : IsIso (κ.app (DerivedCategory.Q.obj K)) := by
      have h : κ.app (DerivedCategory.Q.obj K) =
          H.map e.hom ≫ κ.app N.obj ≫ T.map e.inv := by
        apply (cancel_mono (T.map e.hom)).1
        rw [Category.assoc, Category.assoc, ← T.map_comp, e.inv_hom_id, T.map_id]
        erw [Category.comp_id]
        exact (κ.naturality e.hom).symm
      rw [h]
      infer_instance
    obtain ⟨P, q, hP, hflat, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) K
    have := hq
    let P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory :=
      ⟨P, hP, fun i ↦ (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso _ (P.X i)).symm (hflat i)⟩
    have hcomparison : IsIso (inverseImagePullbackComparison l E g
        (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) K P' q) := by
      rw [← hres K P' q]
      exact hκK
    have := integralSigmaIsIso D l E K
    have hformula :=
      (frobeniusPointTransportIntegral_existsUnique D l hl E N.obj).choose_spec.1 K P' q e
    change IsIso ((frobeniusPointTransportIntegral_existsUnique D l hl E N.obj).choose)
    rw [hformula]
    dsimp only [frobeniusPointTransportIntegralComplex]
    infer_instance

end WeilConjectures
