/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
import all WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteRingSectionDeformation
import all WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
import WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionIntegratedSpecializationIntegrationBaseChange
public import WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesCartesianPair

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

variable [HasCompactification g]

end Section

end FiniteSmoothPurity
end Etale
end AlgebraicGeometry

namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

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
normal cone with the pulled-back conormal bundle. Keep the normal-fibre map supplied by
this very Rees map throughout the calculation; no independence from an arbitrary
Cartesian lift is needed. Finite-ring section deformation gives
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
  classical
  let P := FiniteRingSectionDeformation.sectionFamily d g s hs
  let P' := FiniteRingSectionDeformation.sectionFamily d g' s' hs'
  let φ := SectionReesBaseChange.pairMap s s' q b hsec
  have hφ := SectionReesBaseChange.pairMap_isPullback d g g' s s' hs hs' b q cart hsec
  have hc := SectionReesBaseChange.pairMap_compatible g g' s s' q b hsec cart.w
  obtain ⟨ν, _, _, hν, hπ, hzero, _⟩ := hc.2.2.2
  have sqν : IsPullback ν (Scheme.Hom.normalConeProj g' s')
      (Scheme.Hom.normalConeProj g s) b := by
    have outer := (Scheme.Hom.isPullback_normalConeToDeformationSpace g' s').paste_horiz hφ
    rw [AffineSpace.zeroSection_comp_map, ← hν] at outer
    exact IsPullback.of_right outer hπ
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s)
  let e : ExceptionalFamilyBaseChange P P' b := {
    ambient := ⟨φ, hφ, hc.2.1⟩
    fibre := fun t ↦ match t with
      | false => ⟨ν, sqν, hzero⟩
      | true => ⟨q, cart, hsec⟩
    point_comm := by
      intro t
      cases t
      · exact (AffineSpace.zeroSection_comp_map b).symm
      · exact (AffineSpace.oneSection_comp_map b).symm
    fibre_comm := by
      intro t
      cases t
      · exact hν
      · exact hc.2.2.1.symm }
  have hk : P.IsNormalized A κ ∧ ∀ τ, P.IsNormalized A τ → τ = κ := by
    refine ⟨(FiniteRingSectionDeformation.sectionFamily_normalized_iff A d g s hs κ).2 hκ, ?_⟩
    intro τ hτ
    have ht := (FiniteRingSectionDeformation.sectionFamily_normalized_iff A d g s hs τ).1 hτ
    exact (FiniteRingSectionDeformation.existsUnique_normalized N hN A hA hS d g s hs).unique
      ht hκ
  have hk' : P'.IsNormalized A κ' ∧ ∀ τ, P'.IsNormalized A τ → τ = κ' := by
    refine ⟨(FiniteRingSectionDeformation.sectionFamily_normalized_iff
      A d g' s' hs' κ').2 hκ', ?_⟩
    intro τ hτ
    have ht := (FiniteRingSectionDeformation.sectionFamily_normalized_iff
      A d g' s' hs' τ).1 hτ
    exact (FiniteRingSectionDeformation.existsUnique_normalized N hN A hA hS'
      d g' s' hs').unique ht hκ'
  have hinv (x : S) : IsUnit (N : S.presheaf.stalk x) := by
    simpa only [map_natCast] using hS.map (S.presheaf.germ ⊤ x (by trivial)).hom
  have hδ := (sectionExceptional_normalized_baseChange A N hN hA P P' hinv b e
    κ κ' hk hk').2.symm
  simp only [ExceptionalSectionFamily.specialization, ExceptionalSectionFamily.fibreMap,
    FiniteRingSectionDeformation.sectionExceptionalComparison_eq,
    P, P', FiniteRingSectionDeformation.sectionFamily, e,
    exceptionalFamilyPoint] at hδ
  change (ordinaryFinitePullback A b).map
      (NoetherianSectionSpecialization.specialization A g s κ) ≫
      NoetherianSectionSpecialization.sectionMap A
        (Scheme.Hom.normalConeProj g s) (Scheme.Hom.normalConeProj g' s') b ν sqν
        s.normalConeZeroSection s'.normalConeZeroSection hzero =
      NoetherianSectionSpecialization.sectionMap A g g' b q cart s s' hsec ≫
        NoetherianSectionSpecialization.specialization A g' s' κ' at hδ
  have hn : IsIso (normalSectionMap A d g s hs sq) :=
    normalSectionMap_isIso A d g s hs sq N hN hA hS
  have hn' : IsIso (normalSectionMap A d g' s' hs' sq') :=
    normalSectionMap_isIso A d g' s' hs' sq' N hN hA hS'
  let _ := hn
  let _ := hn'
  have hio := normalExchange_integration A N hN hA d g g' s s' hs hs' b q cart
    hsec sq sq' hS hS' ν sqν hzero hn hn'
  simp only [integratedSpecialization]
  rw [Functor.map_comp]
  rw [Category.assoc]
  rw [hio]
  rw [← Category.assoc]
  rw [hδ]
  simp only [Category.assoc]

end AlgebraicGeometry.Etale.FiniteSmoothPurity
