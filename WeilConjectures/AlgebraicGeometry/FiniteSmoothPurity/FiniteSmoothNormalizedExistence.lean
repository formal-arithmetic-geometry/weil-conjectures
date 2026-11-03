/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionIntegratedSpecialization
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange

/-! Existence by the explicit diagonal, deformation and bundle construction.
(blueprint: lem-sp-finite-smooth-normalized-existence). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The normalized diagonal/Rees construction over a finite coefficient ring.
Source: general-ring purity, construction of the ordinary orientation
(blueprint: lem-sp-finite-smooth-normalized-existence). -/
theorem generalRingNormalizedOrientation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (hX : IsUnit (N : Γ(X, ⊤))) :
    ∃ (G : FiniteRingSectionDeformation.Geometry d
        (pullback.fst f f) (pullback.diagonal f))
      (alpha : dualizingComplex A f ≅ line A N hA X d),
      OrientationNormalized A N hN hA f d G hX alpha := by
  let G := FiniteRingSectionDeformation.geometry d (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f)
  have := G
  obtain ⟨κ, hκ, _⟩ := FiniteRingSectionDeformation.existsUnique_normalized
    N hN A hA hX d (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)
  have : HasInvertibleExponent A X := ⟨N, hN, hA, hX⟩
  have : IsIso (dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f f).flip) := by
    have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension
      A f d (IsPullback.of_hasPullback f f).flip
    exact (isIso_dualizingComplexBaseChangeMap_iff A _).2 inferInstance
  have : IsIso (finiteSmoothDiagonalFactor A f) := by
    unfold finiteSmoothDiagonalFactor
    simp only [← Iso.app_inv]
    infer_instance
  have := FiniteRingSectionDeformation.isIso_specialization
    N hN A hA hX d (pullback.fst f f) (pullback.diagonal f)
      (pullback.diagonal_fst f) κ hκ
  let q := reesConeComparison (pullback.diagonal f) ≪≫
    FiniteRingSectionDeformation.coneBundleIso d (pullback.fst f f) (pullback.diagonal f)
  have hq : q.hom ≫ VectorBundleZeroSection.π X d
      (ConormalGradedAlgebra.piece (pullback.diagonal f) 1) =
      Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f) := by
    dsimp [q]
    rw [Category.assoc,
      (FiniteRingSectionDeformation.coneBundleIso_spec d (pullback.fst f f)
        (pullback.diagonal f) (pullback.diagonal_fst f)).1,
      (reesConeComparison_spec (pullback.diagonal f)).1]
    exact Scheme.Hom.purityNormalProjection_eq _ _ (pullback.diagonal_fst f)
  have sq : IsPullback q.hom
      (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
      (VectorBundleZeroSection.π X d (ConormalGradedAlgebra.piece (pullback.diagonal f) 1))
      (𝟙 X) := IsPullback.of_horiz_isIso ⟨by simpa using hq⟩
  have := normalSectionMap_isIso A d (pullback.fst f f) (pullback.diagonal f)
    (pullback.diagonal_fst f) sq N hN hA hX
  have := (FiniteRingSectionDeformation.bundleAdjoint_isIso
    N hN A hA X hX d (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)).2
  let alpha : dualizingComplex A f ≅ line A N hA X d :=
    asIso (finiteSmoothDiagonalFactor A f) ≪≫
      asIso (NoetherianSectionSpecialization.specialization A
        (pullback.fst f f) (pullback.diagonal f) κ) ≪≫
      (asIso (normalSectionMap A d (pullback.fst f f) (pullback.diagonal f)
        (pullback.diagonal_fst f) sq)).symm ≪≫
      FiniteRingSectionDeformation.bundleOrientation N hN A hA X hX d
        (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)
  refine ⟨G, alpha, κ, hκ, sq, ?_⟩
  dsimp [alpha, FiniteRingSectionDeformation.bundleOrientation]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]


end AlgebraicGeometry.Etale.FiniteSmoothPurity
