/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
import Sheaf.AlgebraicGeometry.Morphisms.PuncturedMatchingChartSectionInjective

/-! # Kernel torsion for the punctured matching projection

Source: Stacks Project, Tags 0BLH and 05ER, localized chart comparison.
(blueprint: lem-sbc-punctured-matching-chart-kernel-torsion)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

set_option backward.isDefEq.respectTransparency false in
private theorem principalOpen_sections_localization
    {B : CommRingCat.{u}} {X : Scheme.{u}} (j : X ⟶ Spec B)
    [IsOpenImmersion j] (r : B)
    (hj : j ''ᵁ (⊤ : X.Opens) = PrimeSpectrum.basicOpen r) :
    let := ((ΓSpecIso B).inv ≫ j.appTop).hom.toAlgebra
    IsLocalization.Away r Γ(X, ⊤) := by
  let e : Γ(Spec B, PrimeSpectrum.basicOpen r) ≅ Γ(X, ⊤) :=
    (Spec B).presheaf.mapIso (eqToIso hj).op ≪≫ j.appIso ⊤
  have he : e.hom.hom.comp (algebraMap B Γ(Spec B, PrimeSpectrum.basicOpen r)) =
      ((ΓSpecIso B).inv ≫ j.appTop).hom := by
    simp only [IsAffineOpen.algebraMap_Spec_obj, ← CommRingCat.hom_comp]
    congr 1
    apply (cancel_mono (j.appIso ⊤).inv).mp
    simp only [e, Iso.trans_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [show j.appTop = j.appLE ⊤ ⊤ le_rfl by simp [Hom.appLE],
      Hom.appLE_appIso_inv]
    simp [← Functor.map_comp]
  have hloc := (IsLocalization.isLocalization_iff_of_ringEquiv
    (Submonoid.powers r) e.commRingCatIsoToRingEquiv).mp inferInstance
  convert hloc using 1
  exact Algebra.algebra_ext _ _ (fun b => congrArg (fun k : B →+* Γ(X, ⊤) => k b) he.symm)

private theorem principalOpen_image
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (f : A)
    (hf : (PrimeSpectrum.basicOpen f : (Spec (.of A)).Opens) ≤ U) :
    let W := (D.modelMap ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f)
    (W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι) ''ᵁ (⊤ : W.toScheme.Opens) =
      PrimeSpectrum.basicOpen (D.baseMap.hom f) := by
  dsimp only
  rw [Hom.comp_image, Opens.ι_image_top, image_morphismRestrict_preimage]
  rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι,
    inf_eq_right.mpr hf]
  exact SpecMap_preimage_basicOpen D.baseMap f

/-- A matching section vanishing on the f-chart is killed by a power of f.

Source: Stacks Project, Tag 05ER, the localized chart comparison in its proof,
using 05EP and 05EQ; the geometric charts are those of Tag 0BLH.
Proof: choose a finite generating family of the maximal ideal and include f,
which belongs to the ideal because hf excludes the closed point from D(f).
Use the affine inverse images under q and the affine scheme E to form the
formal-gluing datum given by D.overlapIso. The sheaf equalizer identifies its
H0 with D.matchingRing. Functoriality of appTop and the Spec–Γ adjunction
identify the f-coordinate of b with ψ(ρ b). If it is zero, its completed
coordinate becomes zero after localization at f by the injectivity of the
overlap equivalence, and each other chart coordinate becomes zero after
localization at f by its overlap equation with the f-chart. Each coordinate
is therefore killed by some power of f. There are finitely many coordinates,
so the maximum of their exponents kills the entire compatible family.
Under the equalizer identification scalar multiplication by f is
multiplication by D.baseMap.hom f; the claimed equation follows. Equivalently,
apply the injectivity part of exists_unique_bijective_h0_localization and the
zero criterion for module localization. This argument uses no chart lifting.
For f = 0 the exponent 1 works. For any nilpotent f, an exponent annihilating
f works. The zero ring and empty charts are included.
(blueprint: lem-sbc-punctured-matching-chart-kernel-torsion) -/
theorem puncturedMatching_chart_kernel_torsion
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (f : A)
    (hf : (PrimeSpectrum.basicOpen f : (Spec (.of A)).Opens) ≤ U) :
    let W := (D.modelMap ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f)
    let ρ := ((ΓSpecIso D.matchingRing).inv ≫
      (W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι).appTop).hom
    let ψ := (D.puncturedMap ∣_ W).appTop.hom
    ∀ b : D.matchingRing, ψ (ρ b) = 0 →
      ∃ n : ℕ, D.baseMap.hom f ^ n * b = 0 := by
  classical
  dsimp
  let W := (D.modelMap ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f)
  let j := W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι
  let ρ := ((ΓSpecIso D.matchingRing).inv ≫ j.appTop).hom
  let r := D.baseMap.hom f
  let : Algebra D.matchingRing Γ(W.toScheme, ⊤) := ρ.toAlgebra
  have hloc : IsLocalization.Away r Γ(W.toScheme, ⊤) :=
    principalOpen_sections_localization j r (principalOpen_image D f hf)
  intro b hb
  have hz : ρ b = 0 := puncturedMatching_chart_section_injective hU D f hf b hb
  have hz0 : ρ b = ρ 0 := by simpa only [map_zero] using hz
  have hz' : (algebraMap D.matchingRing Γ(W.toScheme, ⊤)) b =
      (algebraMap D.matchingRing Γ(W.toScheme, ⊤)) 0 := by
    have hmap : (algebraMap D.matchingRing Γ(W.toScheme, ⊤)) = ρ := rfl
    rw [hmap]
    exact hz0
  obtain ⟨s, hs⟩ := IsLocalization.exists_of_eq (R := D.matchingRing)
    (M := Submonoid.powers r) (S := Γ(W.toScheme, ⊤)) hz'
  have hsprop := s.property
  rw [Submonoid.mem_powers_iff] at hsprop
  obtain ⟨n, hn⟩ := hsprop
  refine ⟨n, ?_⟩
  have hs' : (r ^ n : D.matchingRing) * b = 0 := by
    simpa [hn, Algebra.smul_def, mul_comm] using hs
  exact hs'

end AlgebraicGeometry.Scheme.CompletionGluingData
