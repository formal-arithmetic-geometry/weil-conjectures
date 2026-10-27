/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.AlgebraicGeometry.NodalLocalTangentGrading
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations

/-!
# Uniqueness from the normalized homogeneous-fraction formula

Source: Stacks Project, curves.tex, Tag 0CBT, comparison of constructions (2) and (3).
(blueprint: lem-sfb-nodal-normalized-chart-uniqueness).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.NodalLocal

/-- A power of a parameter generating the extended maximal ideal divides every
representative of the corresponding graded piece.
Source: Stacks Project, curves.tex, Tag 0CBT, homogeneous division formula.
(blueprint: lem-sfb-nodal-normalized-chart-uniqueness) -/
theorem exists_normalization_division (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) (hgen : normalizationIdeal A = Ideal.span {algebraMap A (Normalization A) f})
    (n : ℕ) (a : ↥((IsLocalRing.maximalIdeal A) ^ n)) :
    ∃ b : Normalization A,
      algebraMap A (Normalization A) a.val = algebraMap A (Normalization A) f ^ n * b := by
  have ha := Ideal.mem_map_of_mem (algebraMap A (Normalization A)) a.property
  rw [Ideal.map_pow] at ha
  change algebraMap A (Normalization A) a.val ∈ normalizationIdeal A ^ n at ha
  rw [hgen, Ideal.span_singleton_pow] at ha
  exact Ideal.mem_span_singleton.mp ha

/-- On one admissible chart the normalized fraction formula fixes the residue map.
Source: Stacks Project, curves.tex, Tag 0CBT, homogeneous division formula.
(blueprint: lem-sfb-nodal-normalized-chart-uniqueness) -/
theorem normalized_chart_equiv_unique
    (A : Type u) [CommRing A] [IsLocalRing A] [GradedRing (tangentGrading A)]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hlinear : initialForm A 1 ⟨f, by simpa using hf⟩ ∈ tangentGrading A 1)
    (hgen : normalizationIdeal A = Ideal.span {algebraMap A (Normalization A) f})
    (θ ψ : HomogeneousLocalization.Away (tangentGrading A)
      (initialForm A 1 ⟨f, by simpa using hf⟩) ≃+* ResidueAlgebra A)
    (hθ : ∀ (n : ℕ) (a : ↥((IsLocalRing.maximalIdeal A) ^ n))
      (ha : initialForm A n a ∈ tangentGrading A (n • (1 : ℕ))) (b : Normalization A),
      algebraMap A (Normalization A) a.val = algebraMap A (Normalization A) f ^ n * b →
      θ (HomogeneousLocalization.Away.mk (tangentGrading A) hlinear n
        (initialForm A n a) ha) = Ideal.Quotient.mk (normalizationIdeal A) b)
    (hψ : ∀ (n : ℕ) (a : ↥((IsLocalRing.maximalIdeal A) ^ n))
      (ha : initialForm A n a ∈ tangentGrading A (n • (1 : ℕ))) (b : Normalization A),
      algebraMap A (Normalization A) a.val = algebraMap A (Normalization A) f ^ n * b →
      ψ (HomogeneousLocalization.Away.mk (tangentGrading A) hlinear n
        (initialForm A n a) ha) = Ideal.Quotient.mk (normalizationIdeal A) b) : θ = ψ := by
  apply RingEquiv.ext
  intro z
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (tangentGrading A) hlinear z
  simp only [smul_eq_mul, mul_one] at ha
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, hb⟩ := exists_normalization_division A f hgen n a
  exact (hθ n a _ b hb).trans (hψ n a _ b hb).symm

/-- A normalized comparison is unique when an admissible parameter chart covers Proj.
Source: Stacks Project, curves.tex, Tag 0CBT, homogeneous division formula.
(blueprint: lem-sfb-nodal-normalized-chart-uniqueness) -/
theorem normalized_iso_unique
    (A : Type u) [CommRing A] [IsLocalRing A] [GradedRing (tangentGrading A)]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hlinear : initialForm A 1 ⟨f, by simpa using hf⟩ ∈ tangentGrading A 1)
    (hreg : algebraMap A (Normalization A) f ∈ nonZeroDivisors (Normalization A))
    (hgen : normalizationIdeal A = Ideal.span {algebraMap A (Normalization A) f})
    (hcover : Proj.basicOpen (tangentGrading A)
      (initialForm A 1 ⟨f, by simpa using hf⟩) = ⊤)
    (i j : Proj (tangentGrading A) ≅ Spec (.of (ResidueAlgebra A)))
    (hi : IsNormalized A i) (hj : IsNormalized A j) : i = j := by
  obtain ⟨θ, hθ, hi⟩ := hi f hf hlinear hreg hgen
  obtain ⟨ψ, hψ, hj⟩ := hj f hf hlinear hreg hgen
  have heq := normalized_chart_equiv_unique A f hf hlinear hgen θ ψ hθ hψ
  subst ψ
  apply Iso.ext
  have hι : IsIso (Proj.basicOpen (tangentGrading A)
      (initialForm A 1 ⟨f, by simpa using hf⟩)).ι := by
    rw [hcover]
    change IsIso (Scheme.topIso _).hom
    infer_instance
  apply (cancel_epi (Proj.basicOpen (tangentGrading A)
    (initialForm A 1 ⟨f, by simpa using hf⟩)).ι).mp
  exact hi.trans hj.symm

/-- Normalized fractions force the comparison to lie over the canonical residue map.
Source: Stacks Project, curves.tex, Tag 0CBT, degree-zero part of the chart formula.
(blueprint: lem-sfb-nodal-normalized-chart-uniqueness) -/
theorem normalized_iso_over_residue
    (A : Type u) [CommRing A] [IsLocalRing A] [GradedRing (tangentGrading A)]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hlinear : initialForm A 1 ⟨f, by simpa using hf⟩ ∈ tangentGrading A 1)
    (hreg : algebraMap A (Normalization A) f ∈ nonZeroDivisors (Normalization A))
    (hgen : normalizationIdeal A = Ideal.span {algebraMap A (Normalization A) f})
    (hcover : Proj.basicOpen (tangentGrading A)
      (initialForm A 1 ⟨f, by simpa using hf⟩) = ⊤)
    (i : Proj (tangentGrading A) ≅ Spec (.of (ResidueAlgebra A)))
    (hi : IsNormalized A i) :
    i.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (IsLocalRing.ResidueField A) (ResidueAlgebra A))) =
        Proj.toSpecZero (tangentGrading A) ≫
          Spec.map (CommRingCat.ofHom (tangentZeroIso A).toRingHom) := by
  obtain ⟨θ, hθ, hi⟩ := hi f hf hlinear hreg hgen
  let ℓ := initialForm A 1 ⟨f, by simpa using hf⟩
  let z := HomogeneousLocalization.fromZeroRingHom (tangentGrading A) (Submonoid.powers ℓ)
  have hθzero : θ.toRingHom.comp z =
      (algebraMap (IsLocalRing.ResidueField A) (ResidueAlgebra A)).comp
        (tangentZeroIso A).symm.toRingHom := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := (tangentZeroIso A).surjective x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha : initialForm A 0 ⟨a, by simp⟩ ∈ tangentGrading A (0 • (1 : ℕ)) := by
      exact ⟨Submodule.Quotient.mk ⟨a, by simp⟩, rfl⟩
    have hz : z (tangentZeroIso A (IsLocalRing.residue A a)) =
        HomogeneousLocalization.Away.mk (tangentGrading A) hlinear 0
          (initialForm A 0 ⟨a, by simp⟩) ha := by
      apply HomogeneousLocalization.val_injective
      simp [z, HomogeneousLocalization.fromZeroRingHom,
        HomogeneousLocalization.Away.mk, ℓ, tangentZeroIso_apply]
      rfl
    change θ (z (tangentZeroIso A (IsLocalRing.residue A a))) = _
    rw [hz]
    have h := hθ 0 ⟨a, by simp⟩ ha (algebraMap A (Normalization A) a) (by simp)
    change _ = algebraMap (IsLocalRing.ResidueField A) (ResidueAlgebra A)
      ((tangentZeroIso A).symm (tangentZeroIso A (IsLocalRing.residue A a)))
    rw [RingEquiv.symm_apply_apply]
    exact h
  have hι : IsIso (Proj.basicOpen (tangentGrading A) ℓ).ι := by
    rw [show Proj.basicOpen (tangentGrading A) ℓ = ⊤ from hcover]
    change IsIso (Scheme.topIso _).hom
    infer_instance
  have haway : IsIso (Proj.awayι (tangentGrading A) ℓ hlinear (by decide)) := by
    unfold Proj.awayι
    infer_instance
  apply (cancel_epi (Proj.awayι (tangentGrading A) ℓ hlinear (by decide))).mp
  have hii : Proj.awayι (tangentGrading A) ℓ hlinear (by decide) ≫ i.hom =
      Spec.map (CommRingCat.ofHom θ.symm.toRingHom) := by
    rw [Proj.awayι, Category.assoc, hi]
    simp
  rw [← Category.assoc, hii, ← Category.assoc, Proj.awayι_toSpecZero]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  have h := DFunLike.congr_fun hθzero (tangentZeroIso A a)
  simpa using (congrArg θ.symm h).symm

end AlgebraicGeometry.NodalLocal
