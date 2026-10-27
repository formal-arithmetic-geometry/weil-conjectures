/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.Paper.FiniteRingSectionDeformation
public import Sheaf.SecSmoothPurity.DncCoefficientTransportData
import Sheaf.SecSmoothPurity.SectionScalarBaseChange
import Sheaf.SecSmoothPurity.FiniteSectionFamilyConstancy
import Sheaf.SecSmoothPurity.ScalarSectionCompositor

/-! # Canonical normalized finite-section scalar transport

Source: blueprint/latest, smooth-purity reduction compatibility proof (3), Orientation,
and general-ring proof (2), Steps 4--7.
(blueprint: new-lem-sp-finite-section-specialization-scalar-canonical).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The canonical normalized B-comparison satisfies the scalar specialization square.

This is the canonical construction step in the general-ring argument: scalar/base-change
squares identify the one and zero fibre mates; finite-family constancy and shifted-line
rigidity construct the unique normalized B-family comparison; restricting its conjugation
identity to the zero fibre gives the displayed equation. The construction is independent
of any supplied normalized B-comparison, which is recovered by uniqueness in the parent
lemma. Empty bases, zero rings, and rank zero use the same canonical maps.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, (3), Orientation, and
sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.proof.md, (2), Steps 4--7.
(blueprint: new-lem-sp-finite-section-specialization-scalar-canonical). -/
theorem finiteSectionSpecialization_scalar_canonical
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [HasCompactification g] [IsSeparated g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s]
    [FiniteRingSectionDeformation.Geometry d g s] (hs : s ≫ g = 𝟙 S)
    (hS : IsUnit (N : Γ(S, ⊤)))
    (κ : NoetherianSectionSpecialization.family A g s ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
        (sectionInvariant A g s))
    (hκ : NoetherianSectionSpecialization.Normalized A g s hs κ) :
    ∃ κB : NoetherianSectionSpecialization.family B g s ≅
      (ordinaryFinitePullback B (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
        (sectionInvariant B g s),
      NoetherianSectionSpecialization.Normalized B g s hs κB ∧
      WeilConjectures.DncCoefficientTransport.sectionMap φ g s ≫
          NoetherianSectionSpecialization.specialization B g s κB =
        (scalarExtension φ S).map
            (NoetherianSectionSpecialization.specialization A g s κ) ≫
          WeilConjectures.DncCoefficientTransport.sectionMap φ
            (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection := by
  sorry

end AlgebraicGeometry.Etale.FiniteSmoothPurity
