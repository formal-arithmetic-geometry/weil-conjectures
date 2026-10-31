/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
import WeilConjectures.SixFunctors.Etale.Derived.DualityPullback
import WeilConjectures.EtaleCohomology.Purity.Smooth.WeilEquivariance
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence

/-! # The smooth oriented duality-pullback comparison

The functorial dualizing tensor map and the given orientation provide smooth
purity. Composing its inverse with the existing ambient duality-pullback
comparison proves the final clause of cor-sf-duality-pullback.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable (k : Type u) [Field k]

private lemma dualizingTensor_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] {K K' : DerivedCategoryModule Λ Y} (v : K ⟶ K') :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (dualizingComplex Λ f)).map
        ((L((f)^*[ModuleCat.{u + 1} Λ])).map v) ≫ dualizingComplexTensorMap Λ f K' =
      dualizingComplexTensorMap Λ f K ≫ (R(f)^![Λ]).map v := by
  have h := Adjunction.projectionTensorMap_naturality_right
    (rightDerivedUpperShriekAdjunction Λ f) _
    (projectionMap_app_app_naturality_right f) (𝟙_ _) v
  unfold dualizingComplexTensorMap lowerShriekRightAdjointUnitTensorMap
  dsimp only [lowerShriekRightAdjointTensorMap] at *
  erw [← Category.assoc, h]
  simp only [Category.assoc]
  erw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact congrArg (R(f)^![Λ]).map (MonoidalCategory.leftUnitor_naturality v)

/-- The functorial smooth-purity comparison supplies the oriented clause of the
corollary.
Proof: naturality of the projection tensor map and of the left unitor gives
naturality of the dualizing tensor map. Its components are invertible by the
smooth tensor theorem. Tensor symmetry puts this natural isomorphism in the
orientation convention; `smoothPurityIso_hom_naturality` then assembles the
oriented functor isomorphism. Invert it, compose with the existing ambient
comparison, and restrict by the finite-Tor inclusion.
Source: the final proof step of `cor-sf-duality-pullback`
(blueprint: lem-sf-duality-pullback-smooth-oriented). -/
theorem duality_pullback_smooth_orientation_core [IsAlgClosed k]
    [HasTateTwist Λ] [HasInvertibleExponent Λ (Spec (.of k))] :
    ∀ (C : OrientationComparisonData Λ) (_O : OrientationDatum Λ C)
      {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
      [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
      [HasCompactification aX] [IsSeparated aY] [LocallyOfFiniteType aY]
      [QuasiCompact aY] [HasCompactification aY] (f : X ⟶ Y)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [HasCompactification f] (_hf : f ≫ aY = aX) (d : ℕ)
      [SmoothOfRelativeDimension d f],
      Nonempty ((DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} Λ) Y).ι.op ⋙
          L((f)^*[ModuleCat.{u + 1} Λ]).op ⋙ verdierDual Λ aX ≅
        (DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} Λ) Y).ι.op ⋙
          verdierDual Λ aY ⋙ L((f)^*[ModuleCat.{u + 1} Λ]) ⋙
          twistShift Λ X d) := by
  intro C O X Y aX aY _ _ _ _ _ _ _ _ f _ _ _ _ hf d _
  subst aX
  have : HasInvertibleExponent Λ X := HasInvertibleExponent.of_hom (f ≫ aY)
  obtain ⟨beta⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) X
  have htheta := (exists_dualizingComplex_iso_and_tensor Λ f d).choose_spec.2.2.2
  let thetaMap : L((f)^*[ModuleCat.{u + 1} Λ]) ⋙
      (derivedTensor (ModuleCat.{u + 1} Λ) X).obj (dualizingComplex Λ f) ⟶
      R(f)^![Λ] :=
    { app K := dualizingComplexTensorMap Λ f K
      naturality _ _ v := dualizingTensor_naturality Λ f v }
  have : ∀ K, IsIso (thetaMap.app K) := htheta
  have : IsIso thetaMap := NatIso.isIso_of_isIso_app thetaMap
  let theta := asIso thetaMap
  let tensorFormula : L((f)^*[ModuleCat.{u + 1} Λ]) ⋙
      (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj (dualizingComplex Λ f) ≅
      R(f)^![Λ] :=
    NatIso.ofComponents (fun K ↦
      (beta.app ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).app (dualizingComplex Λ f) ≪≫
        theta.app K) (fun v ↦ by
          have h := NatTrans.congr_app
            (beta.hom.naturality ((L((f)^*[ModuleCat.{u + 1} Λ])).map v))
            (dualizingComplex Λ f)
          dsimp only [NatTrans.comp_app] at h
          dsimp only [Iso.trans_hom, Iso.app_hom, Functor.comp_map]
          erw [← Category.assoc, h, Category.assoc]
          simp only [Category.assoc]
          congr 1
          exact theta.hom.naturality v)
  let purity : L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ X d ≅ R(f)^![Λ] :=
    NatIso.ofComponents (fun K ↦ smoothPurityIso Λ f K
      (O.orientation f d).twistShiftIso.symm (tensorFormula.app K))
      (fun v ↦ smoothPurityIso_hom_naturality Λ f
        (O.orientation f d).twistShiftIso.symm tensorFormula v)
  obtain ⟨e⟩ := nonempty_iso_verdierDual_leftDerivedUpperStar Λ f aY
  exact ⟨Functor.isoWhiskerLeft _ e ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ purity.symm)⟩

end AlgebraicGeometry.Etale
