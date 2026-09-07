/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# `HomogeneousLocalization.Away.map` and the base algebra structure

We show that `HomogeneousLocalization.Away.map` is compatible with the canonical ring
homomorphisms from the degree-zero subrings, and that it is surjective as soon as the
graded ring homomorphism it is built from is.

Moreover, if `A` is a graded algebra over a base ring `R`, we endow `HomogeneousLocalization`
with the induced `R`-algebra structure, via the degree-zero part `𝒜 0`.
-/

@[expose] public section

namespace HomogeneousLocalization.Away

variable {ι A B σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] [DecidableEq ι] [AddCommMonoid ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- `HomogeneousLocalization.Away.map` is compatible with the canonical ring homomorphisms
from the degree-zero subrings. -/
lemma map_comp_fromZeroRingHom (g : 𝒜 →+*ᵍ ℬ) (s : A) :
    (HomogeneousLocalization.Away.map g s).comp
        (fromZeroRingHom 𝒜 (Submonoid.powers s)) =
      (fromZeroRingHom ℬ (Submonoid.powers (g s))).comp g.gradeZeroRingHom := by
  ext a
  simp [fromZeroRingHom, HomogeneousLocalization.Away.map, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk]

/-- If `g : 𝒜 →+*ᵍ ℬ` is surjective, so is the induced map `(A_s)₀ → (B_{g s})₀` on the
degree-zero parts of the localizations away from a homogeneous element `s`.

Every element of `(B_{g s})₀` is a fraction `b / (g s) ^ n` with `b` homogeneous of degree
`n • d`, and `b` lifts to a homogeneous element of `𝒜 (n • d)` by
`GradedRingHom.exists_mem_of_surjective`. -/
theorem map_surjective (g : 𝒜 →+*ᵍ ℬ) (hg : Function.Surjective g) {d : ι} {s : A}
    (hs : s ∈ 𝒜 d) : Function.Surjective (HomogeneousLocalization.Away.map g s) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (g.map_mem hs) z
  obtain ⟨a, ha, rfl⟩ := GradedRingHom.exists_mem_of_surjective hg hb
  exact ⟨Away.mk 𝒜 hs n a ha, by rw [Away.map_mk]⟩

end HomogeneousLocalization.Away

namespace HomogeneousLocalization

section Algebra

variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommMonoid ι]
  [DecidableEq ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (x : Submonoid A)

@[simp]
lemma val_fromZeroRingHom (a : 𝒜 0) :
    (fromZeroRingHom 𝒜 x a).val = algebraMap A (Localization x) (a : A) := by
  simp only [fromZeroRingHom, ← Localization.mk_one_eq_algebraMap]
  rfl

/-- If `A` is a graded `R`-algebra, its homogeneous localization at a submonoid of `A` is an
`R`-algebra, via the degree-zero part `𝒜 0`. -/
instance : Algebra R (HomogeneousLocalization 𝒜 x) where
  algebraMap := (fromZeroRingHom 𝒜 x).comp (algebraMap R (𝒜 0))
  smul := (· • ·)
  commutes' _ _ := mul_comm _ _
  smul_def' r z := by
    obtain ⟨c, rfl⟩ := mk_surjective z
    apply val_injective
    simp [val_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply R A (Localization x)]

lemma algebraMap_eq' :
    algebraMap R (HomogeneousLocalization 𝒜 x) =
      (fromZeroRingHom 𝒜 x).comp (algebraMap R (𝒜 0)) :=
  rfl

@[simp]
lemma val_algebraMap (r : R) :
    (algebraMap R (HomogeneousLocalization 𝒜 x) r).val = algebraMap R (Localization x) r := by
  rw [algebraMap_eq']
  simp [IsScalarTower.algebraMap_apply R A (Localization x)]

instance : IsScalarTower R (HomogeneousLocalization 𝒜 x) (Localization x) :=
  .of_algebraMap_eq fun r ↦ (val_algebraMap 𝒜 x r).symm

end Algebra

end HomogeneousLocalization
