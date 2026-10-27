/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteSmoothPurityMaps
public import Sheaf.Paper.VectorPurityNormalization
import all Sheaf.Paper.FiniteRingSectionDeformation
import all Sheaf.Paper.SectionReesBaseChangeEtale
import Sheaf.Paper.SectionReesCartesianPair
import Sheaf.Paper.SmoothSectionExchangeIndependence

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The normalized zero-fibre specialization square for the normal exchange, with
invertible annihilator as in the finite-coefficient DNC theorem.
Source: sk-prop-sp-purity-bc, proof (1), and finite-ring section deformation.
(blueprint: lem-sp-finite-section-integrated-specialization-specialization-factor).
Proof: the coefficientwise Rees map of the Cartesian pair is Cartesian over the affine
lines. Its restrictions at one and zero give the original pair map and a canonical
normal-cone map. Apply exceptional-family base-change coherence to these three squares.
Uniqueness of the normalized family trivializations makes their transported comparison
agree at one and hence everywhere. Restriction at zero gives the required specialization
identity for the canonical normal map. Finally, two Cartesian lifts of the normal pair
have equal section comparisons: their quotient is an automorphism fixing its zero
section, which acts trivially on the section dualizing line. This replaces the canonical
normal map by the supplied map. The integer N is invertible on the new base by pullback.
No orientation base-change or integrated-specialization theorem is used. -/
theorem specialization_normalExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S V' S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S']
    (hS : IsUnit (N : Γ(S, ⊤)))
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
    (ν : s'.ker.normalCone ⟶ s.ker.normalCone)
    (sqν : IsPullback ν (Scheme.Hom.normalConeProj g' s')
      (Scheme.Hom.normalConeProj g s) b)
    (hzero : s'.normalConeZeroSection ≫ ν = b ≫ s.normalConeZeroSection)
    (κ : NoetherianSectionSpecialization.family A g s ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
        (sectionInvariant A g s))
    (κ' : NoetherianSectionSpecialization.family A g' s' ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).obj
        (sectionInvariant A g' s'))
    (hκ : NoetherianSectionSpecialization.Normalized A g s hs κ)
    (hκ' : NoetherianSectionSpecialization.Normalized A g' s' hs' κ') :
    (ordinaryFinitePullback A b).map
        (NoetherianSectionSpecialization.specialization A g s κ) ≫
      NoetherianSectionSpecialization.sectionMap A
        (Scheme.Hom.normalConeProj g s) (Scheme.Hom.normalConeProj g' s') b ν sqν
        s.normalConeZeroSection s'.normalConeZeroSection hzero =
      NoetherianSectionSpecialization.sectionMap A g g' b q cart s s' hsec ≫
        NoetherianSectionSpecialization.specialization A g' s' κ' := by
  classical
  let P := FiniteRingSectionDeformation.sectionFamily d g s hs
  let P' := FiniteRingSectionDeformation.sectionFamily d g' s' hs'
  let φ := SectionReesBaseChange.pairMap s s' q b hsec
  have hφ := SectionReesBaseChange.pairMap_isPullback d g g' s s' hs hs' b q cart hsec
  have hc := SectionReesBaseChange.pairMap_compatible g g' s s' q b hsec cart.w
  obtain ⟨ν₀, l, haff, hν₀, hπ, hz₀, hrest⟩ := hc.2.2.2
  have sq₀ : IsPullback ν₀ (Scheme.Hom.normalConeProj g' s')
      (Scheme.Hom.normalConeProj g s) b := by
    have outer := (Scheme.Hom.isPullback_normalConeToDeformationSpace g' s').paste_horiz hφ
    rw [AffineSpace.zeroSection_comp_map, ← hν₀] at outer
    exact IsPullback.of_right outer hπ
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s)
  let e : ExceptionalFamilyBaseChange P P' b := {
    ambient := ⟨φ, hφ, hc.2.1⟩
    fibre := fun t ↦ match t with
      | false => ⟨ν₀, sq₀, hz₀⟩
      | true => ⟨q, cart, hsec⟩
    point_comm := by
      intro t
      cases t
      · exact (AffineSpace.zeroSection_comp_map b).symm
      · exact (AffineSpace.oneSection_comp_map b).symm
    fibre_comm := by
      intro t
      cases t
      · exact hν₀
      · exact hc.2.2.1.symm }
  have hS' : IsUnit (N : Γ(S', ⊤)) := by
    simpa only [map_natCast] using hS.map b.appTop.hom
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
  have h := (sectionExceptional_normalized_baseChange A N hN hA P P' hinv b e
    κ κ' hk hk').2.symm
  simp only [ExceptionalSectionFamily.specialization, ExceptionalSectionFamily.fibreMap,
    FiniteRingSectionDeformation.sectionExceptionalComparison_eq,
    P, P', FiniteRingSectionDeformation.sectionFamily, e,
    exceptionalFamilyPoint] at h
  change (ordinaryFinitePullback A b).map
      (NoetherianSectionSpecialization.specialization A g s κ) ≫
      NoetherianSectionSpecialization.sectionMap A
        (Scheme.Hom.normalConeProj g s) (Scheme.Hom.normalConeProj g' s') b ν₀ sq₀
        s.normalConeZeroSection s'.normalConeZeroSection hz₀ = _ at h
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g' s') :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g' s') inferInstance
  have : IsSeparated (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @IsSeparated)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have : IsSeparated (Scheme.Hom.normalConeProj g' s') :=
    MorphismProperty.of_isPullback (P := @IsSeparated)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g' s') inferInstance
  rw [NoetherianSectionSpecialization.sectionMap_eq_of_cartesian A N hN hA d
    (Scheme.Hom.normalConeProj g s) (Scheme.Hom.normalConeProj g' s')
    s.normalConeZeroSection s'.normalConeZeroSection
    (Scheme.Hom.normalConeZeroSection_normalConeProj hs)
    (Scheme.Hom.normalConeZeroSection_normalConeProj hs') hS b ν ν₀ sqν sq₀ hzero hz₀]
  exact h

end AlgebraicGeometry.Etale.FiniteSmoothPurity
