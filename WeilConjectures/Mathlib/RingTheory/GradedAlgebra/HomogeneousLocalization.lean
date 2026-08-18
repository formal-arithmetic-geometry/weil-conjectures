/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# `HomogeneousLocalization.Away.map`

We show that `HomogeneousLocalization.Away.map` is compatible with the canonical ring
homomorphisms from the degree-zero subrings, and that it is surjective as soon as the
graded ring homomorphism it is built from is.
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
