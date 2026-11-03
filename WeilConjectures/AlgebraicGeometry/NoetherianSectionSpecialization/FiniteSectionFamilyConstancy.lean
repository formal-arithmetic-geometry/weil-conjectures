/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization
import all WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization

/-! # Constancy of the section family for any finite coefficient ring

The ordinary shifted-line descent argument works for every finite ring with an
invertible annihilator, including the zero ring and rings nonflat over Z/ell^n.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.NoetherianSectionSpecialization

/-- The canonical fibre maps and the uniquely normalized family comparison for a
finite ring with invertible annihilator.
Source: blueprint/latest, sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md,
Local construction and Gluing; coefficient argument in sk-thm-smooth-purity-general-ring,
Proof (2) (blueprint: lem-pur-finite-section-family-constancy).
Proof: the Rees projection is smooth of the same dimension as g. Smooth exceptional
base change makes both actual fibre maps invertible. The local dualizing comparisons
identify the source and family with locally constant free rank-one sheaves after
removing [2d]. On a centered etale coordinate cover, normalize each comparison by
its value at one. Shifted-line normalized descent glues these comparisons and proves
uniqueness by rigidity along the connected affine-line fibres. None of these steps
requires the coefficient ring to be a prime-power quotient or to be nonzero. -/
theorem finite_family_constancy
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)] :
    IsIso (atOne A g s hs) ∧ IsIso (atZero A g s) ∧
      ∃! κ : family A g s ≅
        (upperStar (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
            (sectionInvariant A g s), Normalized A g s hs κ := by
  classical
  have : HasInvertibleExponent A S := ⟨N, hN, hA, hS⟩
  have : HasInvertibleExponent A s.ker.deformationSpace :=
    HasInvertibleExponent.of_hom (s.ker.deformationSpaceProj ≫ g)
  have hD := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  have : IsNoetherian (AffineSpace (ULift.{u} (Fin 1)) S) :=
    isNoetherian_of_locallyOfFiniteType (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
  have : IsNoetherian s.ker.deformationSpace :=
    isNoetherian_of_locallyOfFiniteType (Scheme.Hom.deformationSpaceProj g s)
  have := compact_normalProjection d g s hs
  have hlines := SectionLocalDualizingComparisons.section_local_dualizing_comparisons
    A N hN hA hS d g s hs
  have hOne : IsIso (atOne A g s hs) := hlines.2.2.1
  have hZero : IsIso (atZero A g s) :=
    isIso_sectionMap A (Scheme.Hom.deformationSpaceProj g s) d
      (Scheme.Hom.normalConeProj g s) (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
      s.ker.normalConeToDeformationSpace
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s)
      s.deformationSpaceSection s.normalConeZeroSection
      Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace
  obtain ⟨cover, local_exists⟩ := local_comparisons_exist A N hN hA hS d g s hs
  let theta := asIso (atOne A g s hs)
  choose normalized hnormalized using fun x : cover.I₀ ↦
    normalize_chart A (cover.f x) (sectionInvariant A g s) (family A g s)
      theta (local_exists x).some
  obtain ⟨kappa, hkappa, _, huniq, _⟩ :=
    (AffineLineNormalizedDescent.normalized_descent A S (2 * (d : ℤ))
      (sectionInvariant A g s) (family A g s)
      (line_shape A d S _ hlines.1) (line_shape A d _ _ hlines.2.1) theta cover
      normalized hnormalized).2.2
  exact ⟨hOne, hZero, kappa, hkappa, huniq⟩

end AlgebraicGeometry.Etale.NoetherianSectionSpecialization
