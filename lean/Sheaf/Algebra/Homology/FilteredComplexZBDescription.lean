/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Sheaf.CategoryTheory.FilteredComplexSpectralSequence
import Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries
import Sheaf.Algebra.Homology.FilteredComplexQuotientImageComparison

/-!
# Cycles and boundaries of a filtered complex

Source: Stacks Project, Homology, Tag 012K, Lemma on the filtered-complex spectral sequence
and its displayed cycle-boundary formulas (blueprint: lem-sp-filtered-complex-ZB-description).
-/

@[expose] public section

universe vZ uZ

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

private theorem complexSubobjects_stabilize
    {C : Type uZ} [Category.{vZ} C] [Abelian C]
    {K : CochainComplex C ℤ} (F : DecreasingFiltration K) (hF : F.IsFinite)
    (p n : ℤ) :
    ∃ (R : ℤ) (_hR : 1 ≤ R), ∀ r : ℤ, R ≤ r →
      F.complexCycles p n r = F.complexCycles p n R ∧
      F.complexBoundaries p n r = F.complexBoundaries p n R := by
  obtain ⟨a, b, ha, hb⟩ := hF
  have hbot (i : ℤ) (hi : b ≤ i) : F.step i = ⊥ := by
    apply le_antisymm _ bot_le
    simpa only [hb] using F.antitone_step hi
  have htop (i : ℤ) (hi : i ≤ a) : F.step i = ⊤ := by
    apply le_antisymm le_top
    simpa only [ha] using F.antitone_step hi
  let R := max 1 (max (b - p) (p + 1 - a))
  have hR : 1 ≤ R := le_max_left _ _
  have hRb : b - p ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRa : p + 1 - a ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨R, hR, ?_⟩
  intro r hr
  have hhi : F.step (p + r) = F.step (p + R) := by
    rw [hbot (p + r) (by omega), hbot (p + R) (by omega)]
  have hlo : F.step (p - r + 1) = F.step (p - R + 1) := by
    rw [htop (p - r + 1) (by omega), htop (p - R + 1) (by omega)]
  have hhi' : F.complexStep (p + r) (n + 1) = F.complexStep (p + R) (n + 1) :=
    congrArg (fun S : Subobject K ↦ imageSubobject (S.arrow.f (n + 1))) hhi
  have hlo' : F.complexStep (p - r + 1) (n - 1) =
      F.complexStep (p - R + 1) (n - 1) :=
    congrArg (fun S : Subobject K ↦ imageSubobject (S.arrow.f (n - 1))) hlo
  constructor
  · simp only [complexCycles, hhi']
  · simp only [complexBoundaries, hlo']

private theorem cokernelOfLE_iso_of_eq
    {C : Type uZ} [Category.{vZ} C] [Abelian C] {A : C}
    {B Z B' Z' : Subobject A} (h : B ≤ Z) (h' : B' ≤ Z')
    (hB : B = B') (hZ : Z = Z') :
    Nonempty (cokernel (Subobject.ofLE B Z h) ≅ cokernel (Subobject.ofLE B' Z' h')) := by
  subst B'
  subst Z'
  exact ⟨Iso.refl _⟩

/-- Cycles, boundaries, quotient-complex image description, first page and stabilization.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-ZB-description).

Proof: (1) Apply the graded differential-object construction of
`lem-sp-filtered-complex-associated-spectral-sequence-construction` to the bigraded object
with component `Fᵖ⁺¹Kᵖ⁺¹⁺q` and shift inclusion into `FᵖKᵖ⁺¹⁺q`. This gives the spectral
sequence with differential of bidegree `(r, 1-r)` and initial page `grᵖKᵖ⁺q`.
(2) Unwind its kernels and images to obtain the displayed cycle and boundary subobjects.
The square-zero differential sends every boundary to zero, so `Bᵣ ≤ Zᵣ`; the page is their
quotient. These steps use the construction node and `def-sp-filtration`.
(3) A representative in `Fᵖ ∩ d⁻¹(Fᵖ⁺ʳ)` is a cocycle modulo `Fᵖ⁺ʳ` and also modulo
`Fᵖ⁺¹` since `r ≥ 1`. Its target cohomology class vanishes precisely when it is `dy + f`
with `y ∈ Fᵖ⁻ʳ⁺¹` and `f ∈ Fᵖ⁺¹`. Then `dy = x-f` lies in `Fᵖ ∩ d(Fᵖ⁻ʳ⁺¹)`.
Conversely such a boundary is a cycle because `d²=0`. Thus the image has exactly the kernel
of the projection onto `Zᵣ/Bᵣ`. The induced isomorphism is specified below on these
representatives, so it is the natural comparison, rather than an arbitrary object
isomorphism. This uses `def-sp-abelian` and `def-sp-filtration`.
(4) For `r=1`, the conditions become the kernel and image of the graded differential,
giving the homology of the graded complex. For fixed `p,q`, finiteness of the filtration
(`def-sp-filtration`), hence in degrees `p+q+1` and `p+q-1`, makes the two filtration
tails respectively zero and the whole object for large `r`; hence both subobjects, and
consequently their quotient pages, stabilize. -/
theorem filteredComplex_ZB_description
    {C : Type uZ} [Category.{vZ} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (hF : F.IsFinite) :
    ∃ E : CohomologicalSpectralSequence C 0,
      (∀ p n : ℤ,
        F.complexCycles p n 1 = kernelSubobject ((F.gradedPiece p).d n (n + 1)) ∧
        F.complexBoundaries p n 1 = imageSubobject ((F.gradedPiece p).d (n - 1) n)) ∧
      (∀ p q : ℤ,
        Nonempty ((E.page 1).X (p, q) ≅ (F.gradedPiece p).homology (p + q))) ∧
      (∀ (p q r : ℤ) (hr : 1 ≤ r),
        let n := p + q
        let Z := F.complexCycles p n r
        let B := F.complexBoundaries p n r
        ∃ hBZ : B ≤ Z,
          Nonempty ((E.page r (le_trans (show 0 ≤ 1 from zero_le_one) hr)).X (p, q) ≅
            cokernel (Subobject.ofLE B Z hBZ)) ∧
          ∃ (ha : p - r + 1 ≤ p) (hb : p + 1 ≤ p + r),
            let hs := (Int.le_add_one (show p ≤ p from le_rfl)).trans hb
            let ht := ha.trans (Int.le_add_one (show p ≤ p from le_rfl))
            let S := F.complexQuotient p (p + r) hs
            let T := F.complexQuotient (p - r + 1) (p + 1) ht
            ∃ φ : S ⟶ T,
              F.complexQuotientπ p (p + r) hs ≫ φ =
                Subobject.ofLE (F.step p) (F.step (p - r + 1)) (F.antitone_step ha) ≫
                  F.complexQuotientπ (p - r + 1) (p + 1) ht ∧
              let R := F.complexCycleRepresentatives p n r
              let Hφ := HomologicalComplex.homologyMap φ n
              ∃ (z : (R : C) ⟶ (Z : C)) (g : (R : C) ⟶ S.cycles n),
                z ≫ Z.arrow = R.arrow ≫
                  (F.complexQuotientπ p (p + 1) (Int.le_add_one (show p ≤ p from le_rfl))).f n ∧
                g ≫ S.iCycles n = R.arrow ≫ (F.complexQuotientπ p (p + r) hs).f n ∧
                ∃ e : cokernel (Subobject.ofLE B Z hBZ) ≅ image Hφ,
                  z ≫ cokernel.π (Subobject.ofLE B Z hBZ) ≫ e.hom ≫ image.ι Hφ =
                    g ≫ S.homologyπ n ≫ Hφ) ∧
      (∀ p q : ℤ, ∃ (R : ℤ) (hR : 1 ≤ R), ∀ (r : ℤ) (hr : R ≤ r),
        F.complexCycles p (p + q) r = F.complexCycles p (p + q) R ∧
        F.complexBoundaries p (p + q) r = F.complexBoundaries p (p + q) R ∧
        Nonempty
          ((E.page r (le_trans (le_trans (show 0 ≤ 1 from zero_le_one) hR) hr)).X (p, q) ≅
            (E.page R (le_trans (show 0 ≤ 1 from zero_le_one) hR)).X (p, q))) := by
  obtain ⟨E, _, _, hpages⟩ := filteredComplex_associated_spectralSequence K F
  have hfirst := filteredComplex_firstPage_cycles_boundaries F
  refine ⟨E, hfirst, ?_, ?_, ?_⟩
  · intro p q
    obtain ⟨hBZ, ⟨e⟩⟩ := hpages p q 1 le_rfl
    have hcmp := filteredComplex_quotient_image_comparison F p (p + q) 1 le_rfl hBZ
    dsimp only at hcmp
    generalize hx : p - 1 + 1 = a at hcmp
    have hap : a = p := by omega
    clear hx
    subst a
    obtain ⟨ha, hb, φ, hφ, z, g, hz, hg, eH, heH⟩ := hcmp
    let π := F.complexQuotientπ p (p + 1) (Int.le_add_one le_rfl)
    let : Epi π := by
      dsimp [π, complexQuotientπ]
      infer_instance
    have hφid : φ = 𝟙 (F.complexQuotient p (p + 1) (Int.le_add_one le_rfl)) := by
      apply (cancel_epi π).1
      simpa only [π, Subobject.ofLE_refl, Category.id_comp, Category.comp_id] using hφ
    subst φ
    exact ⟨e ≪≫ eH ≪≫ image.eqToIso (HomologicalComplex.homologyMap_id _ _) ≪≫
      imageMonoIsoSource (𝟙 ((F.complexQuotient p (p + 1)
        (Int.le_add_one le_rfl)).homology (p + q)))⟩
  · intro p q r hr
    obtain ⟨hBZ, he⟩ := hpages p q r hr
    exact ⟨hBZ, he, filteredComplex_quotient_image_comparison F p (p + q) r hr hBZ⟩
  · intro p q
    obtain ⟨R, hR, hstable⟩ := complexSubobjects_stabilize F hF p (p + q)
    refine ⟨R, hR, ?_⟩
    intro r hr
    obtain ⟨hZ, hB⟩ := hstable r hr
    obtain ⟨hBZr, ⟨er⟩⟩ := hpages p q r (hR.trans hr)
    obtain ⟨hBZR, ⟨eR⟩⟩ := hpages p q R hR
    obtain ⟨equot⟩ := cokernelOfLE_iso_of_eq hBZr hBZR hB hZ
    exact ⟨hZ, hB, ⟨er ≪≫ equot ≪≫ eR.symm⟩⟩

end CategoryTheory.DecreasingFiltration
