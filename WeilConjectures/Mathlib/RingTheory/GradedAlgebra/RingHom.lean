/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# The degree-zero component of a graded ring homomorphism

We define `GradedRingHom.gradeZeroRingHom`, the degree-zero component of a graded ring
homomorphism as a ring homomorphism between the degree-zero subrings.
-/

@[expose] public section

namespace GradedRingHom

variable {ι A B σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] [DecidableEq ι] [AddCommMonoid ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The degree-zero component of a graded ring homomorphism, as a ring homomorphism
between the degree-zero subrings. -/
def gradeZeroRingHom (f : 𝒜 →+*ᵍ ℬ) : 𝒜 0 →+* ℬ 0 where
  toFun a := ⟨f a, f.map_mem a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[simp]
lemma coe_gradeZeroRingHom_apply (f : 𝒜 →+*ᵍ ℬ) (a : 𝒜 0) :
    (f.gradeZeroRingHom a : B) = f a :=
  rfl

end GradedRingHom
