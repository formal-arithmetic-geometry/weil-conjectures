/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.Paper.FiniteSmoothPurityMaps
public import Sheaf.Paper.VectorPurityNormalization
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
import Sheaf.Paper.FiniteSectionIntegratedSpecializationNormalExchange
import Sheaf.Paper.FiniteSectionIntegratedSpecializationSpecializationBaseChange
import Sheaf.Paper.FiniteSectionIntegratedSpecializationIntegrationBaseChange

/-! # Integrated section specialization with arbitrary finite coefficients

Source: latest blueprint, smooth-purity base-change factors, proof (1).
(blueprint: lem-sp-finite-section-integrated-specialization-base-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

section Section
variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {V S : Scheme.{u}} [IsNoetherian S]
variable (d : ℕ) (g : V ⟶ S)
variable (s : S ⟶ V) [IsClosedImmersion s]
variable [FiniteRingSectionDeformation.Geometry d g s] (hs : s ≫ g = 𝟙 S)
variable (sq : IsPullback
  ((reesConeComparison s ≪≫ FiniteRingSectionDeformation.coneBundleIso d g s).hom)
  (Scheme.Hom.normalConeProj g s)
  (VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1)) (𝟙 S))

/-- The cone-to-bundle section map is invertible, since its horizontal map is an
isomorphism and the bundle projection is smooth.
Source: finite smooth orientation normalization, normal-bundle factor
(blueprint: lem-sp-finite-section-integrated-specialization-base-change). -/
theorem normalSectionMap_isIso (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hS : IsUnit (N : Γ(S, ⊤))) : IsIso (normalSectionMap A d g s hs sq) := by
  let q := reesConeComparison s ≪≫ FiniteRingSectionDeformation.coneBundleIso d g s
  have hq : q.hom ≫ VectorBundleZeroSection.π S d
      (ConormalGradedAlgebra.piece s 1) = Scheme.Hom.normalConeProj g s := by
    simpa only [Category.comp_id] using sq.w
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  let π := VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1)
  have : SmoothOfRelativeDimension d π := by
    apply (MorphismProperty.cancel_left_of_respectsIso
      (@SmoothOfRelativeDimension d) q.hom π).mp
    rw [hq]
    infer_instance
  have : HasInvertibleExponent A S := ⟨N, hN, hA, hS⟩
  have : HasInvertibleExponent A (VectorBundleZeroSection.scheme S d
      (ConormalGradedAlgebra.piece s 1)) := HasInvertibleExponent.of_hom π
  let := (vectorBundlePurityCompactification S d
    (ConormalGradedAlgebra.piece s 1)).hasCompactification
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension A π d sq
  have : IsIso (dualizingComplexBaseChangeMap A sq) :=
    (isIso_dualizingComplexBaseChangeMap_iff A sq).2 inferInstance
  unfold normalSectionMap NoetherianSectionSpecialization.sectionMap
  infer_instance

variable [HasCompactification g]

/-- The actual zero-fibre specialization followed by inverse normal-bundle integration.
Both inverse maps are proved invertible; no orientation is chosen from existence.
Source: smooth-purity base-change factors (1), psi
(blueprint: lem-sp-finite-section-integrated-specialization-base-change). -/
def integratedSpecialization (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hS : IsUnit (N : Γ(S, ⊤)))
    (κ : NoetherianSectionSpecialization.family A g s ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
        (sectionInvariant A g s)) :
    sectionInvariant A g s ⟶ line A N hA S d :=
  letI := normalSectionMap_isIso A d g s hs sq N hN hA hS
  NoetherianSectionSpecialization.specialization A g s κ ≫
    inv (normalSectionMap A d g s hs sq) ≫
      (FiniteRingSectionDeformation.bundleOrientation N hN A hA S hS d
        (ConormalGradedAlgebra.piece s 1)).hom

/-- The defining integration equation for the constructed specialization.
Source: smooth-purity base-change factors (1), psi
(blueprint: lem-sp-finite-section-integrated-specialization-base-change). -/
theorem integratedSpecialization_normalization
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hS : IsUnit (N : Γ(S, ⊤)))
    (κ : NoetherianSectionSpecialization.family A g s ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
        (sectionInvariant A g s)) :
    integratedSpecialization A d g s hs sq N hN hA hS κ ≫
        FiniteRingSectionDeformation.bundleSectionAdjoint N hN A hA S hS d
          (ConormalGradedAlgebra.piece s 1) ≫ normalSectionMap A d g s hs sq =
      NoetherianSectionSpecialization.specialization A g s κ := by
  let := normalSectionMap_isIso A d g s hs sq N hN hA hS
  let := (FiniteRingSectionDeformation.bundleAdjoint_isIso N hN A hA S hS d
    (ConormalGradedAlgebra.piece s 1)).2
  simp only [integratedSpecialization, FiniteRingSectionDeformation.bundleOrientation,
    Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc,
    IsIso.inv_hom_id, Category.comp_id]

end Section

/-- Arbitrary Noetherian base change of the integrated specialization of a closed smooth
section, for a finite ring killed by an invertible positive integer. This compares section
invariants only; it contains no diagonal restriction or orientation of a smooth morphism.

Source: latest blueprint sec-smooth-purity/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-factors.proof.md, proof (1), DNC and vector integration;
lem-sp-section-dnc-integration-square, first displayed square.
(blueprint: lem-sp-finite-section-integrated-specialization-base-change).

Proof: identify the Cartesian pair with the canonical pullback pair by its universal
property. Arbitrary-base-change compatibility of the extended Rees algebra identifies
its families, sections and fibres, and the homogeneous cone comparison identifies its
normal cone with the pulled-back conormal bundle. Finite-ring section deformation gives
the square for the zero specialization: transport the normalized family comparison
through the family exchange, use uniqueness of its normalization at one, and restrict
at zero. The integration adjunct satisfies the exceptional-exchange square because it
is the transpose of the Kummer-normalized integration trace, which commutes with base
change. Restrict this square to the normal zero section and invert its adjuncts. The
homogeneous normal-cone comparison preserves both projection and zero section, so its
section exchange pastes with this square. Compose with the specialization square and
cancel the intervening normal exchange. The resulting composite is exactly the two
integratedSpecialization arrows. Canonical pullback composition and the root-normalized
Tate comparison give the displayed line arrow. This argument works for arbitrary finite
A without scalar flatness; the affine normalization uses tensor balancing, not exactness
of underived scalar extension. Rank zero uses the empty coordinate tower; on empty
schemes or with the zero ring the equations hold in the zero categories. -/
theorem integratedSpecialization_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S V' S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S']
    (d : ℕ) (g : V ⟶ S) (g' : V' ⟶ S')
    [SmoothOfRelativeDimension d g] [SmoothOfRelativeDimension d g']
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    [IsSeparated g'] [QuasiCompact g'] [HasCompactification g']
    (s : S ⟶ V) (s' : S' ⟶ V') [IsClosedImmersion s] [IsClosedImmersion s']
    [FiniteRingSectionDeformation.Geometry d g s]
    [FiniteRingSectionDeformation.Geometry d g' s']
    (hs : s ≫ g = 𝟙 S) (hs' : s' ≫ g' = 𝟙 S')
    (b : S' ⟶ S) (q : V' ⟶ V) (cart : IsPullback q g' g b)
    (hsec : s' ≫ q = b ≫ s)
    (sq : IsPullback
      ((reesConeComparison s ≪≫ FiniteRingSectionDeformation.coneBundleIso d g s).hom)
      (Scheme.Hom.normalConeProj g s)
      (VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1)) (𝟙 S))
    (sq' : IsPullback
      ((reesConeComparison s' ≪≫ FiniteRingSectionDeformation.coneBundleIso d g' s').hom)
      (Scheme.Hom.normalConeProj g' s')
      (VectorBundleZeroSection.π S' d (ConormalGradedAlgebra.piece s' 1)) (𝟙 S'))
    (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤)))
    (κ : NoetherianSectionSpecialization.family A g s ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
        (sectionInvariant A g s))
    (κ' : NoetherianSectionSpecialization.family A g' s' ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).obj
        (sectionInvariant A g' s'))
    (hκ : NoetherianSectionSpecialization.Normalized A g s hs κ)
    (hκ' : NoetherianSectionSpecialization.Normalized A g' s' hs' κ') :
    (ordinaryFinitePullback A b).map
        (integratedSpecialization A d g s hs sq N hN hA hS κ) ≫
        (vectorIntegrationBaseCoefficientPullback A N hA
          (WeilConjectures.PurityFiniteSetting.purityTwistTransport A N hN hA) b hS d).hom =
      NoetherianSectionSpecialization.sectionMap A g g' b q cart s s' hsec ≫
        integratedSpecialization A d g' s' hs' sq' N hN hA hS' κ' := by
  -- `normalExchange_exists` takes the section equations `hs hs'` (G3 statement repair);
  -- the second alternative only serves the pre-repair signature until G3 has landed.
  obtain ⟨ν, sqν, hzero⟩ : ∃ (ν : s'.ker.normalCone ⟶ s.ker.normalCone),
      IsPullback ν (Scheme.Hom.normalConeProj g' s')
        (Scheme.Hom.normalConeProj g s) b ∧
      s'.normalConeZeroSection ≫ ν = b ≫ s.normalConeZeroSection := by
    first
      | exact normalExchange_exists g g' s s' hs hs' b q cart hsec d
      | exact normalExchange_exists g g' s s' b q cart hsec d
  let e := NoetherianSectionSpecialization.sectionMap A
    (Scheme.Hom.normalConeProj g s) (Scheme.Hom.normalConeProj g' s') b ν sqν
    s.normalConeZeroSection s'.normalConeZeroSection hzero
  let qsec := NoetherianSectionSpecialization.sectionMap A g g' b q cart s s' hsec
  let δ := NoetherianSectionSpecialization.specialization A g s κ
  let δ' := NoetherianSectionSpecialization.specialization A g' s' κ'
  let t := (vectorIntegrationBaseCoefficientPullback A N hA
    (WeilConjectures.PurityFiniteSetting.purityTwistTransport A N hN hA) b hS d).hom
  have hn : IsIso (normalSectionMap A d g s hs sq) :=
    normalSectionMap_isIso A d g s hs sq N hN hA hS
  have hn' : IsIso (normalSectionMap A d g' s' hs' sq') :=
    normalSectionMap_isIso A d g' s' hs' sq' N hN hA hS'
  let _ := hn
  let _ := hn'
  have hδ := specialization_normalExchange A N hN hA hS d g g' s s' hs hs' b q cart
    hsec ν sqν hzero κ κ' hκ hκ'
  have hio := normalExchange_integration A N hN hA d g g' s s' hs hs' b q cart
    hsec sq sq' hS hS' ν sqν hzero hn hn'
  simp only [integratedSpecialization]
  rw [Functor.map_comp]
  rw [Category.assoc]
  rw [hio]
  rw [← Category.assoc]
  rw [hδ]
  simp only [Category.assoc]

end FiniteSmoothPurity
end Etale
end AlgebraicGeometry
