/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.SecSmoothPurity.DncCoefficientTransportData

/-! # Scalar compatibility of the canonical exceptional section base-change mate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.DncCoefficientTransport

/-- Scalar extension commutes with the actual exceptional base-change square and
its pullback to any pair of compatible sections.
Source: blueprint/latest, sec-smooth-purity/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-mixed.proof.md, exceptional mate cube, and
sk-thm-smooth-purity-general-ring.proof.md, Proof (2), fibre identifications
(blueprint: lem-pur-section-scalar-base-change).
Proof: transpose the two paths under the primed B compact-support adjunction.
The compact-support coefficient comparison is the composite of the ordinary open
comparison and proper scalar mate. Their base-change cube commutes on K-flat
representatives, with the same inverse-image balancing. The counit equations of
the exceptional coefficient map and base-change mate identify the transposes.
This proves the square at the unit, after its canonical scalar and pullback unit
identifications. Whisker by the primed section pullback; inverse-image composition
and scalar balancing identify s' followed by v with b followed by s, giving the
second equation. These are identities of the specified maps, not choices of
isomorphisms. For a merely locally Noetherian primed base, restrict to its affine
open cover and use canonical inverse-image coherence. This proves the section
identity without imposing quasi-compactness on an etale localization. -/
theorem section_scalar_base_change
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (g : V ⟶ S) [HasCompactification g]
    [IsSeparated g] [QuasiCompact g] (d : ℕ) [SmoothOfRelativeDimension d g] :
    (∀ {S' : Scheme.{u}} [IsNoetherian S'] (b : S' ⟶ S),
      Etale.ExceptionalCoefficients.BaseChangeCompatibility φ g b (𝟙_ _)) ∧
    ∀ {V' S' : Scheme.{u}} [IsLocallyNoetherian S'] (g' : V' ⟶ S')
      [HasCompactification g'] [QuasiCompact g']
      (b : S' ⟶ S) (v : V' ⟶ V) (sq : IsPullback v g' g b)
      (s : S ⟶ V) (s' : S' ⟶ V') (hs : s' ≫ v = b ≫ s),
      (Etale.scalarPullbackIso φ b).inv.app (Etale.sectionInvariant A g s) ≫
          (Etale.upperStar (ModuleCat.{u + 1} B) b).leftDerivedFunctor.map
            (sectionMap φ g s) ≫
          Etale.NoetherianSectionSpecialization.sectionMap B g g' b v sq s s' hs =
        (Etale.scalarExtension φ S').map
            (Etale.NoetherianSectionSpecialization.sectionMap A g g' b v sq s s' hs) ≫
          sectionMap φ g' s' := by sorry

end WeilConjectures.DncCoefficientTransport
