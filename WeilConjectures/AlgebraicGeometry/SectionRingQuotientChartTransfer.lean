/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.SectionRingSecondChartGenerator
import WeilConjectures.AlgebraicGeometry.SectionRingChartCrossMultiplication

/-! # Verification of section-ring quotients on a second chart

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

private theorem sectionRing_power_generator {X : Scheme.{v}} (L : X.Modules)
    [L.IsInvertible] {e : ℕ} (t : sectionRingGrade L e) (W : X.Opens)
    (ht : IsFreeGenerator ((L.tensorPow e).presheaf.map
      (homOfLE (le_top : W ≤ ⊤)).op (t.val e))) (k : ℕ) :
    IsFreeGenerator ((L.tensorPow (k • e)).presheaf.map
      (homOfLE (le_top : W ≤ ⊤)).op ((t.val ^ k) (k • e))) := by
  induction k with
  | zero =>
    rw [show (0 : ℕ) • e = 0 from zero_nsmul e, pow_zero]
    rw [DirectSum.one_def, DirectSum.of_eq_same]
    change IsFreeGenerator ((L.tensorPow 0).presheaf.map
      (homOfLE (le_top : W ≤ ⊤)).op (unitSectionsEquiv ⊤ 1))
    intro V hV
    rw [presheaf_map_map_apply]
    erw [presheaf_map_unitSectionsEquiv, map_one]
    have hf : (fun r : Γ(X, V) ↦ r • unitSectionsEquiv (X := X) V 1) =
        unitSectionsEquiv (X := X) V := by
      funext r
      exact (unitSectionsEquiv_eq_smul_one r).symm
    rw [hf]
    exact (unitSectionsEquiv V).bijective
  | succ k ih =>
    rw [succ_nsmul, pow_succ]
    have hm : (t.val ^ k * t.val) (k • e + e) =
        (L.tensorPowAddIso (k • e) e).inv.app ⊤
          (tmulSection ((t.val ^ k) (k • e)) (t.val e)) := by
      obtain ⟨tk, htk⟩ := (show sectionRingGrade L (k • e) from
        ⟨t.val ^ k, SetLike.pow_mem_graded k t.property⟩).property
      change DirectSum.of _ _ tk = t.val ^ k at htk
      obtain ⟨t', ht'⟩ := t.property
      rw [← htk, ← ht', DirectSum.of_mul_of, DirectSum.of_eq_same,
        DirectSum.of_eq_same, DirectSum.of_eq_same]
      rfl
    rw [hm, ← Hom.app_presheaf_map, tmulSection_map]
    exact (ih.tmulSection ht).app_hom (L.tensorPowAddIso (k • e) e).symm

-- Elaborating the ambient-open section identifications and tensor cancellation needs this limit.
/-- The coefficient equation on the chosen chart determines all other chart equations. -/
theorem sectionRing_quotient_chart_transfer
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (hd : 0 < d) (U : X.Opens)
    (hs : IsFreeGenerator ((L.tensorPow d).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op (s.val d)))
    (ρ : HomogeneousLocalization.Away (sectionRingGrade L) s.val →+* Γ(X, U))
    (hρ : ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
      ρ (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
          ξ.val ξ.property) •
        (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          ((s.val ^ n) (n • d)) =
      (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (ξ.val (n • d)))
    (q : U.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away
      (sectionRingGrade L) s.val)))
    (hq : (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away
        (sectionRingGrade L) s.val))).inv ≫ q.appTop =
      CommRingCat.ofHom ρ ≫ U.topIso.inv) :
    let g := q ≫ Proj.awayι (sectionRingGrade L) s.val s.property hd
    ∀ (e : ℕ) (_he : 0 < e) (t : sectionRingGrade L e)
        (n : ℕ) (ξ : sectionRingGrade L (n • e)),
        (show Γ(X, U.ι ''ᵁ (g ⁻¹ᵁ
            Proj.basicOpen (sectionRingGrade L) t.val)) from
          g.app (Proj.basicOpen (sectionRingGrade L) t.val)
          (Proj.awayToSection (sectionRingGrade L) t.val
            (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
              ξ.val ξ.property))) •
          (L.tensorPow (n • e)).presheaf.map (homOfLE
            (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
              ⊤)).op ((t.val ^ n) (n • e)) =
        (L.tensorPow (n • e)).presheaf.map (homOfLE
          (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
            ⊤)).op (ξ.val (n • e)) := by
  dsimp only
  intro e he t n ξ
  let g := q ≫ Proj.awayι (sectionRingGrade L) s.val s.property hd
  let W := U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val)
  let k := n * (d - 1)
  have ht := sectionRing_second_chart_generator X L d s hd U hs ρ hρ q hq e he t
  have hk := sectionRing_power_generator L t W ht k
  have hc := sectionRing_chart_cross_multiplication X L d s hd U hs ρ hρ q hq
    e he t n ξ
  dsimp only at hc
  have hm : (ξ.val * t.val ^ k) (n • e + k • e) =
      (L.tensorPowAddIso (n • e) (k • e)).inv.app ⊤
        (tmulSection (ξ.val (n • e)) ((t.val ^ k) (k • e))) := by
    obtain ⟨ξ', hξ⟩ := ξ.property
    obtain ⟨tk', htk⟩ := (show sectionRingGrade L (k • e) from
      ⟨t.val ^ k, SetLike.pow_mem_graded k t.property⟩).property
    change DirectSum.of _ _ tk' = t.val ^ k at htk
    rw [← hξ, ← htk, DirectSum.of_mul_of, DirectSum.of_eq_same,
      DirectSum.of_eq_same, DirectSum.of_eq_same]
    rfl
  rw [hm, ← Hom.app_presheaf_map, tmulSection_map] at hc
  erw [← Hom.app_smul] at hc
  have hi := (bijective_app_of_iso (L.tensorPowAddIso (n • e) (k • e)).symm W).1 hc
  apply hk.injective_tmulSection_right (M := L.tensorPow (n • e)) (le_refl W)
  simpa only [presheaf_map_id_apply, smul_tmulSection] using hi


end AlgebraicGeometry.Scheme.Modules
