/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyMaps
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisInjectiveSectionsExact
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisSectionComparison
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# A section-complex diagram computing étale Mayer–Vietoris pullback

Source: Stacks Project, Tag 0A50.
-/

@[expose] public section

universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- A morphism of short exact nonnegative section complexes, with homology
identifications respecting the prescribed restriction and pullback maps.
(Stacks, Tag 0A50) -/
theorem etale_mayerVietoris_section_diagram
    {X Y : Scheme.{u}} (g : Y ⟶ X) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ SX SY : ShortComplex (CochainComplex AddCommGrpCat.{u + 1} ℕ),
    ∃ φ : SX ⟶ SY, SX.ShortExact ∧ SY.ShortExact ∧
    ∃ eAX : ∀ q : ℕ, SX.X₁.homology q ≃+ Sheaf.H G q,
    ∃ eBX : ∀ q : ℕ, SX.X₂.homology q ≃+
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} U.ι).obj G) q ×
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} V.ι).obj G) q),
    ∃ eCX : ∀ q : ℕ, SX.X₃.homology q ≃+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (U ⊓ V).ι).obj G) q,
    ∃ eAY : ∀ q : ℕ, SY.X₁.homology q ≃+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} g).obj G) q,
    ∃ eBY : ∀ q : ℕ, SY.X₂.homology q ≃+
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ U).ι).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q ×
       Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ V).ι).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q),
    ∃ eCY : ∀ q : ℕ, SY.X₃.homology q ≃+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ (U ⊓ V)).ι).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q,
    (∀ q x, eBX q (HomologicalComplex.homologyMap SX.f q x) =
      (cohomologyMap U.ι G q (eAX q x), cohomologyMap V.ι G q (eAX q x))) ∧
    (∀ q x, eCX q (HomologicalComplex.homologyMap SX.g q x) =
      openCohomologyRestriction (inf_le_left : U ⊓ V ≤ U) G q (eBX q x).1 -
        openCohomologyRestriction (inf_le_right : U ⊓ V ≤ V) G q (eBX q x).2) ∧
    (∀ q x, eBY q (HomologicalComplex.homologyMap SY.f q x) =
      (cohomologyMap (g ⁻¹ᵁ U).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G) q (eAY q x),
       cohomologyMap (g ⁻¹ᵁ V).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G) q (eAY q x))) ∧
    (∀ q x, eCY q (HomologicalComplex.homologyMap SY.g q x) =
      openCohomologyRestriction (g.preimage_mono (inf_le_left : U ⊓ V ≤ U))
        ((upperStar AddCommGrpCat.{u + 1} g).obj G) q (eBY q x).1 -
      openCohomologyRestriction (g.preimage_mono (inf_le_right : U ⊓ V ≤ V))
        ((upperStar AddCommGrpCat.{u + 1} g).obj G) q (eBY q x).2) ∧
    (∀ q x, eAY q (HomologicalComplex.homologyMap φ.τ₁ q x) =
      cohomologyMap g G q (eAX q x)) ∧
    (∀ q x, eCY q (HomologicalComplex.homologyMap φ.τ₃ q x) =
      openCohomologyPullback g (U ⊓ V) G q (eCX q x)) := by
  let I := injectiveResolution G
  let J := injectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G)
  let SX := etaleSectionShortComplex U V I.cocomplex
  let SY := etaleSectionShortComplex (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) J.cocomplex
  have hSX : SX.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro q
    exact etaleSectionShortComplex_degreewise_shortExact U V hcover I.cocomplex q
  have hcY : (g ⁻¹ᵁ U) ⊔ (g ⁻¹ᵁ V) = ⊤ := by
    rw [← g.preimage_sup, hcover, g.preimage_top]
  have hSY : SY.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro q
    exact etaleSectionShortComplex_degreewise_shortExact
      (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) hcY J.cocomplex q
  obtain ⟨φ, eAX, eBX, eCX, eAY, eBY, eCY, hrX, hdX, hrY, hdY, hpA, hpC⟩ :=
    etaleSectionShortComplex_pullback_comparison g U V G I J
  exact ⟨SX, SY, φ, hSX, hSY, eAX, eBX, eCX, eAY, eBY, eCY,
    hrX, hdX, hrY, hdY, hpA, hpC⟩

end AlgebraicGeometry.Etale
