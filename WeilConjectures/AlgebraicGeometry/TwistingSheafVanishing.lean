/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.TwistingSheaf
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# The vanishing locus of a homogeneous global section of `𝒪(j)`

Let `𝒜 : ℕ → σ` be a graded ring with underlying ring `A`, and let `a ∈ 𝒜 j` be homogeneous of
degree `j`. `AlgebraicGeometry.Proj.homogeneousSection` attaches to `a` a global section of the
twisting sheaf `𝒪(j)` on `Proj 𝒜`; on `ℙᴺ_A = Proj A[T₀, …, T_N]` these are the homogeneous
coordinates `T₀, …, T_N ∈ Γ(ℙᴺ, 𝒪(1))`. This file identifies the locus where that section does
not vanish: it is the basic open set `D₊(a)`.

Since `𝒪(d)` is built pointwise — a section over `U` is a dependent function `x ↦ sₓ ∈ A_x`
which is locally a fraction of degree `d` — the statement is phrased pointwise as well: the
value `sₓ` of `homogeneousSection ha` at `x` is a **unit of the local ring `A_x`** if and only if
`a ∉ x`. This is the right notion of non-vanishing, and not `sₓ ≠ 0`: the value `a / 1` can be
nonzero in `A_x` while lying in the maximal ideal, which is exactly what "`a` vanishes at `x`"
means. That units are the right test is justified by `Proj.homogeneousSection_apply_eq_mul`: if
`f ∈ 𝒜 j` does not lie in `x`, then `f` trivialises `𝒪(j)` near `x` (this is
`Proj.isIso_app_twistingSheafMul`) and the value of `homogeneousSection ha` at `x` is `a / f`
times the local generator `f`, where `a / f` lives in the local ring `𝒪_{Proj 𝒜, x}` of `Proj 𝒜`
at `x` and is a unit there precisely when `a ∉ x`
(`HomogeneousLocalization.isUnit_iff_isUnit_val`). Working with the value in `A_x` rather than
with the stalk of `𝒪(j)` avoids having to choose such an `f`, and the two agree.

Combined with additivity of `a ↦ homogeneousSection ha`, recorded here as the bundled map
`Proj.homogeneousSectionHom`, this says that on `ℙᴺ` the section `∑ⱼ cⱼ Tⱼ` of `𝒪(1)` vanishes at
a point with homogeneous coordinates `ξ` if and only if `∑ⱼ cⱼ ξⱼ` lies in the homogeneous prime
of that point, i.e. vanishes in the residue field.

## Main results

- `AlgebraicGeometry.Proj.isUnit_homogeneousSection_apply_iff`: the section of `𝒪(j)` attached to
  `a ∈ 𝒜 j` does not vanish at `x` if and only if `x ∈ D₊(a)`.
- `AlgebraicGeometry.Proj.homogeneousSection_apply_mem_maximalIdeal_iff`: dually, it vanishes at
  `x` if and only if `a` lies in the homogeneous prime ideal of `x`.
- `AlgebraicGeometry.Proj.homogeneousSection_apply_eq_mul`: near a point avoided by `f ∈ 𝒜 j`,
  the section attached to `a` is `a / f` times the local generator attached to `f`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Proj

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

open ProjectiveSpectrum.TwistingSheaf

section Additivity

variable (𝒜) in
/-- The homogeneous elements of degree `j` map additively to the global sections of `𝒪(j)`;
this is `AlgebraicGeometry.Proj.homogeneousSection` as an additive monoid homomorphism. -/
def homogeneousSectionHom (j : ℕ) : ↥(𝒜 j) →+ Γ(twistingSheaf 𝒜 j, ⊤) where
  toFun a := homogeneousSection a.2
  map_zero' := Subtype.ext (funext fun _ ↦ Localization.mk_zero _)
  map_add' a b := homogeneousSection_add a.2 b.2

@[simp]
theorem homogeneousSectionHom_apply {j : ℕ} (a : ↥(𝒜 j)) :
    homogeneousSectionHom 𝒜 j a = homogeneousSection a.2 :=
  rfl

@[simp]
theorem homogeneousSection_zero (j : ℕ) :
    homogeneousSection (𝒜 := 𝒜) (zero_mem (𝒜 j)) = 0 :=
  Subtype.ext (funext fun _ ↦ Localization.mk_zero _)

/-- A finite sum of homogeneous elements of degree `j` gives the sum of the corresponding
sections of `𝒪(j)`: on `ℙᴺ` this expresses the section `∑ⱼ cⱼ Tⱼ` in terms of the homogeneous
coordinates. -/
theorem homogeneousSection_sum {ι : Type*} (s : Finset ι) {j : ℕ} (a : ι → ↥(𝒜 j)) :
    homogeneousSection (𝒜 := 𝒜) (∑ i ∈ s, a i).2 =
      ∑ i ∈ s, homogeneousSection (a i).2 :=
  map_sum (homogeneousSectionHom 𝒜 j) a s

end Additivity

variable {j : ℕ} {a : A} (ha : a ∈ 𝒜 j) (x : (⊤ : (Proj 𝒜).Opens))

include ha in
/-- The value of `homogeneousSection ha` at a point `x` is the image of `a` in the local ring
`A_x`. -/
theorem homogeneousSection_apply_eq_algebraMap :
    (homogeneousSection ha).1 x = algebraMap A (atPoint 𝒜 x.1) a :=
  Localization.mk_one_eq_algebraMap a

include ha in
/-- **Fibrewise non-vanishing.** The global section of `𝒪(j)` attached to a homogeneous element
`a` of degree `j` does not vanish at a point `x` of `Proj 𝒜` — that is, its value at `x` is a
unit of the local ring `A_x` — if and only if `x` lies in the basic open set `D₊(a)`. -/
theorem isUnit_homogeneousSection_apply_iff :
    IsUnit ((homogeneousSection ha).1 x) ↔ (x : Proj 𝒜) ∈ Proj.basicOpen 𝒜 a := by
  rw [homogeneousSection_apply_eq_algebraMap ha x,
    IsLocalization.AtPrime.isUnit_to_map_iff (atPoint 𝒜 x.1)
      (x : Proj 𝒜).asHomogeneousIdeal.toIdeal a]
  exact Iff.rfl

include ha in
/-- **Fibrewise vanishing.** The global section of `𝒪(j)` attached to a homogeneous element `a`
of degree `j` vanishes at a point `x` of `Proj 𝒜` — that is, its value at `x` lies in the maximal
ideal of the local ring `A_x` — if and only if `a` lies in the homogeneous prime ideal of `x`. -/
theorem homogeneousSection_apply_mem_maximalIdeal_iff :
    (homogeneousSection ha).1 x ∈ IsLocalRing.maximalIdeal (atPoint 𝒜 x.1) ↔
      a ∈ (x : Proj 𝒜).asHomogeneousIdeal := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_homogeneousSection_apply_iff ha x,
    Proj.mem_basicOpen, not_not]

/-- The non-vanishing locus of the global section of `𝒪(j)` attached to a homogeneous element
`a` of degree `j` is the basic open set `D₊(a)`. -/
theorem setOf_isUnit_homogeneousSection_apply :
    {x : (⊤ : (Proj 𝒜).Opens) | IsUnit ((homogeneousSection ha).1 x)} =
      {x : (⊤ : (Proj 𝒜).Opens) | (x : Proj 𝒜) ∈ Proj.basicOpen 𝒜 a} :=
  Set.ext fun x ↦ isUnit_homogeneousSection_apply_iff ha x

section LocalGenerator

variable {f : A} (hf : f ∈ 𝒜 j) (hx : f ∉ (x : Proj 𝒜).asHomogeneousIdeal)

include ha hf hx in
/-- Near a point `x` avoided by a homogeneous element `f` of degree `j`, the section of `𝒪(j)`
attached to `f` is a local generator, and the section attached to `a ∈ 𝒜 j` is `a / f` times it.
Here `a / f` is an element of the local ring `𝒪_{Proj 𝒜, x}` of `Proj 𝒜` at `x`, acting on the
value at `x` through `HomogeneousLocalization.val`. -/
theorem homogeneousSection_apply_eq_mul :
    (homogeneousSection ha).1 x =
      (HomogeneousLocalization.mk ⟨j, ⟨a, ha⟩, ⟨f, hf⟩, hx⟩ :
        HomogeneousLocalization.AtPrime 𝒜 (x : Proj 𝒜).asHomogeneousIdeal.toIdeal).val *
        (homogeneousSection hf).1 x := by
  rw [homogeneousSection_apply, homogeneousSection_apply, HomogeneousLocalization.val_mk,
    Localization.mk_mul, mul_one]
  exact (Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp [mul_comm]))).symm

include ha hf hx in
/-- The element `a / f` of the local ring `𝒪_{Proj 𝒜, x}` is a unit if and only if `a` avoids the
homogeneous prime ideal of `x`. -/
theorem isUnit_homogeneousLocalization_mk_iff :
    IsUnit (HomogeneousLocalization.mk ⟨j, ⟨a, ha⟩, ⟨f, hf⟩, hx⟩ :
        HomogeneousLocalization.AtPrime 𝒜 (x : Proj 𝒜).asHomogeneousIdeal.toIdeal) ↔
      (x : Proj 𝒜) ∈ Proj.basicOpen 𝒜 a :=
  HomogeneousLocalization.isUnit_mk_iff _ _

end LocalGenerator

end AlgebraicGeometry.Proj
