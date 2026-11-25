/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsSepClosed

import Mathlib.Algebra.Polynomial.Lifts

/-! # Polynomial lifting step for the pointed étale colimit

Polynomial lifting step for surjectivity of the pointed étale colimit: every element of the
separable closure `K` is a simple root of a monic polynomial lifted to the colimit.

## Implementation details

The image of the colimit in `K` is shown to be a subfield containing the image of `κ(p)`;
the minimal polynomial over `κ(p)` is then lifted coefficientwise using
`Polynomial.lifts_and_natDegree_eq_and_monic`. No injectivity of `R → C` is needed.

## References

* [Stacks: Tag 04GW](https://stacks.math.columbia.edu/tag/04GW)
* [Stacks: Tag 00UH](https://stacks.math.columbia.edu/tag/00UH)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Let `ψ` be a ring map from the colimit to `K` compatible with the pointings, such that
elements with nonzero image are units. Then every `a₀ : K` is a simple root of the image
under `ψ` of some monic polynomial over the colimit. -/
theorem etaleResidueTriples_polynomial_lift
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))))
    (hc : IsColimit c)
    (ψ : c.pt →+* K)
    (hψ : ∀ t, ψ.comp (c.ι.app t).hom =
      ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom)
    (hunit : ∀ x : c.pt, ψ x ≠ 0 → IsUnit x) :
    ∀ a₀ : K, ∃ f : Polynomial c.pt, f.Monic ∧
      f.eval₂ ψ a₀ = 0 ∧ f.derivative.eval₂ ψ a₀ ≠ 0 := by
  classical
  have _colimit := hc
  let k := (Spec R).residueField p
  let χ : k →+* K := algebraMap k K
  let t : EtaleResidueTriple R p K (CommRingCat.ofHom χ) :=
    { B := R
      α := 𝟙 R
      etale := by rw [Spec.map_id]; infer_instance
      q := p
      over := by simp
      φ := CommRingCat.ofHom χ
      compatible := by simp }
  have hinv {y : K} (hy : y ∈ ψ.range) : y⁻¹ ∈ ψ.range := by
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨v, hv⟩ := hunit x hy0
    refine ⟨↑v⁻¹, ?_⟩
    apply eq_inv_of_mul_eq_one_left
    rw [← hv, ← map_mul, Units.inv_mul, map_one]
  let η : p.asIdeal.ResidueField →+* K := χ.comp (Spec.residueFieldIso R p).inv.hom
  have hR (r : R) : η (algebraMap R p.asIdeal.ResidueField r) ∈ ψ.range := by
    refine ⟨(c.ι.app t).hom r, ?_⟩
    have ht := DFunLike.congr_fun (hψ t) r
    change ψ ((c.ι.app t).hom r) = _ at ht
    rw [ht]
    change (((ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫
      CommRingCat.ofHom χ).hom) r = _
    have he := Spec.algebraMap_residueFieldIso_inv R p
    have he' := congrArg (fun f ↦ (f ≫ CommRingCat.ofHom χ).hom r) he
    exact he'.symm
  have hres (b : p.asIdeal.ResidueField) : η b ∈ ψ.range := by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (R ⧸ p.asIdeal) b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [map_div₀]
    simpa only [div_eq_mul_inv, Ideal.algebraMap_quotient_residueField_mk] using
      ψ.range.mul_mem (hR a) (hinv (hR b))
  have hcoeff (b : k) : χ b ∈ ψ.range := by
    have h := hres ((Spec.residueFieldIso R p).hom b)
    change χ ((Spec.residueFieldIso R p).inv
      ((Spec.residueFieldIso R p).hom b)) ∈ ψ.range at h
    have he : (Spec.residueFieldIso R p).inv
        ((Spec.residueFieldIso R p).hom b) = b :=
      CommRingCat.inv_hom_apply (Spec.residueFieldIso R p) b
    exact he ▸ h
  intro a₀
  let g := minpoly k a₀
  have hg : g.Monic := minpoly.monic (Algebra.IsSeparable.isIntegral k a₀)
  have hroot : g.eval₂ χ a₀ = 0 := minpoly.aeval k a₀
  have hsep : g.Separable := Algebra.IsSeparable.isSeparable k a₀
  have hlift : g.map χ ∈ Polynomial.lifts ψ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_map]
    exact hcoeff (g.coeff i)
  obtain ⟨f, hf, -, hfm⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlift (hg.map χ)
  refine ⟨f, hfm, ?_, ?_⟩
  · have he := congrArg (Polynomial.eval a₀) hf
    simp only [Polynomial.eval_map] at he
    exact he.trans hroot
  · have he := congrArg (fun q : Polynomial K ↦ q.derivative.eval a₀) hf
    have hd := hsep.eval₂_derivative_ne_zero χ hroot
    simp only [Polynomial.derivative_map, Polynomial.eval_map] at he
    exact he ▸ hd

end AlgebraicGeometry.Scheme
