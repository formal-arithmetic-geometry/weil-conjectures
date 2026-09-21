/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.HyperplaneSection
public import WeilConjectures.AlgebraicGeometry.TwistingSheafInvertible

/-!
# Where a homogeneous coordinate vanishes on `Proj`

Let `𝒜 : ℕ → σ` be a graded ring with underlying ring `A`, and let `a ∈ 𝒜 j`. The element `a`
gives a global section `AlgebraicGeometry.Proj.homogeneousSection` of the twisting sheaf `𝒪(j)`
on `Proj 𝒜` — on `ℙᴺ` these are the homogeneous coordinates `T₀, …, T_N ∈ Γ(ℙᴺ, 𝒪(1))`. This
file identifies the locus where that section vanishes, in the sense of
`AlgebraicGeometry.Scheme.Modules.VanishesAt`, with the complement of the basic open set
`D₊(a)`.

`WeilConjectures/AlgebraicGeometry/TwistingSheaf.lean` already describes the locus where the
*value* of `homogeneousSection ha` at a point `x` — an element of the localization `A_x` of the
whole graded ring, not of the local ring `𝒪_{Proj 𝒜, x}` of the scheme — is a unit
(`AlgebraicGeometry.Proj.isUnit_homogeneousSection_apply_iff`). What is proved here is the
scheme-theoretic form: the germ of the section at `x` lies in `𝔪ₓ 𝒪(j)ₓ` exactly when `a ∈ x`.
This is the form that the theory of invertible sheaves consumes, for instance in
`WeilConjectures/AlgebraicGeometry/Modules/HyperplaneSection.lean`.

The translation between the two goes through a local trivialisation of `𝒪(j)`. If `f` is a
homogeneous element of degree `m` with `m * k = j` and `f ∉ x`, then multiplication by `f ^ k`
is an isomorphism `𝒪_{D₊(f)} ≅ 𝒪(j)|_{D₊(f)}`
(`AlgebraicGeometry.Proj.isIso_unitSmulRestrictHom_sectionPow`) and
`AlgebraicGeometry.Scheme.Modules.vanishesAt_iff_notMem_basicOpen` applies: the section vanishes
at `x` exactly where its coefficient `a / f ^ k` does, and that coefficient is a unit of the
local ring exactly when `a ∉ x`. Such an `f` exists at every point of `Proj 𝒜` as soon as
`AlgebraicGeometry.Proj.IsCoveredByDvdDegree 𝒜 j` holds, which is the case for a polynomial
ring, and more generally whenever the irrelevant ideal is generated in degree one.

## Main results

- `AlgebraicGeometry.Proj.vanishesAt_homogeneousSection_iff_of_mem_basicOpen`: at a point of a
  basic open set `D₊(f)` with `deg f` dividing `j`, the section of `𝒪(j)` attached to `a ∈ 𝒜 j`
  vanishes exactly off `D₊(a)`.
- `AlgebraicGeometry.Proj.not_vanishesAt_homogeneousSection_of_mem_basicOpen`: unconditionally,
  the section attached to `a` does not vanish at any point of `D₊(a)`.
- `AlgebraicGeometry.Proj.vanishesAt_homogeneousSection_iff`: as soon as `Proj 𝒜` is covered by
  basic open sets of homogeneous elements whose degrees divide `j`, the section attached to `a`
  vanishes at a point exactly when that point lies outside `D₊(a)`.
- `AlgebraicGeometry.Proj.setOf_not_vanishesAt_homogeneousSection`: the non-vanishing locus of
  the section attached to `a` is therefore `D₊(a)`, an affine open subset of `Proj 𝒜` when `a`
  has positive degree (`AlgebraicGeometry.Proj.isAffineOpen_basicOpen`).
- `AlgebraicGeometry.Proj.vanishesAt_homogeneousSection_homogeneousSubmodule_iff`: the criterion
  on the projective space `Proj B[Xᵢ]`, where the covering hypothesis is automatic.

## Blueprint

This file contributes the `ℙᴺ \ H ≅ 𝔸ᴺ` step of `prop:deg-ample-positive`, namely
`lem:deg-hyperplane-complement-affine`: the non-vanishing locus of a homogeneous coordinate is
the basic open set `D₊(a)`, which is affine.

## TODO

- Transport the criterion along a morphism of schemes: the blueprint applies it to a closed
  subscheme `X ⊆ ℙᴺ` and the section `i^* s`, so it needs the compatibility of
  `AlgebraicGeometry.Scheme.Modules.VanishesAt` with
  `AlgebraicGeometry.Scheme.Modules.sectionsPullback`, which is general in the morphism and is
  not available yet.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry

universe u

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

namespace Proj

open ProjectiveSpectrum.TwistingSheaf Scheme.Modules

section Vanishing

variable {j : ℕ} {a : A} (ha : a ∈ 𝒜 j)

include ha in
/-- **A homogeneous element vanishes, as a section of `𝒪(j)`, exactly off its basic open set.**
At a point `x` of a basic open set `D₊(f)` with `f` homogeneous of degree `m` and `j = m * k`,
the global section of `𝒪(j)` attached to `a ∈ 𝒜 j` vanishes if and only if `x ∉ D₊(a)`. -/
theorem vanishesAt_homogeneousSection_iff_of_mem_basicOpen {m : ℕ} {f : A} (hf : f ∈ 𝒜 m)
    {k : ℕ} (hjk : j = m * k) {x : Proj 𝒜} (hx : x ∈ Proj.basicOpen 𝒜 f) :
    (twistingSheaf 𝒜 j).VanishesAt (homogeneousSection ha) x ↔ x ∉ Proj.basicOpen 𝒜 a := by
  have hc : (j : ℤ) = m * (k : ℤ) := mod_cast hjk
  have hfk : f ^ k ∉ x.asHomogeneousIdeal := fun h ↦ hx (x.isPrime.mem_of_pow_mem k h)
  have hfkd : f ^ k ∈ 𝒜 j := by
    rw [hjk, mul_comm]
    simpa [smul_eq_mul] using SetLike.pow_mem_graded k hf
  have hWf : ∀ y : (op (Proj.basicOpen 𝒜 f)).unop, f ∉ y.1.asHomogeneousIdeal.toIdeal :=
    fun y ↦ y.2
  set W : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 f
  set g : Γ(twistingSheaf 𝒜 j, W) := sectionPow hf hWf (k : ℤ) hc
  set r : Γ(Proj 𝒜, W) :=
    powCoeff hf hWf (k : ℤ) hc
      ((twistingSheaf 𝒜 j).presheaf.map W.leTop.op (homogeneousSection ha))
  have : IsIso (unitSmulRestrictHom g) :=
    isIso_unitSmulRestrictHom_sectionPow hf le_rfl (k : ℤ) hc
  have hres : (twistingSheaf 𝒜 j).presheaf.map W.leTop.op (homogeneousSection ha) = r • g :=
    (powCoeff_smul_sectionPow hf hWf (k : ℤ) hc _).symm
  -- the coefficient of the section with respect to the generator `f ^ k` is `a / f ^ k`
  have hval : r.1 ⟨x, hx⟩ =
      (HomogeneousLocalization.mk ⟨j, ⟨a, ha⟩, ⟨f ^ k, hfkd⟩, hfk⟩ :
        HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) :=
    powCoeff_res_homogeneousSection_apply hf le_rfl ha k hjk hfkd ⟨x, hx⟩ hfk
  refine (vanishesAt_iff_notMem_basicOpen g (homogeneousSection ha) r hres hx).trans
    (not_congr ?_)
  rw [Scheme.mem_basicOpen _ r x hx, ← isUnit_mk_iff_mem_basicOpen ha x hfkd hfk, ← hval,
    ← Proj.stalkIso'_germ 𝒜 W x hx r]
  exact (MulEquiv.isUnit_map (Proj.stalkIso' 𝒜 x)).symm

include ha in
/-- **A homogeneous element does not vanish, as a section of `𝒪(j)`, on its own basic open
set.** This is the unconditional half of
`AlgebraicGeometry.Proj.vanishesAt_homogeneousSection_iff_of_mem_basicOpen`. -/
theorem not_vanishesAt_homogeneousSection_of_mem_basicOpen {x : Proj 𝒜}
    (hx : x ∈ Proj.basicOpen 𝒜 a) :
    ¬ (twistingSheaf 𝒜 j).VanishesAt (homogeneousSection ha) x := fun h ↦
  (vanishesAt_homogeneousSection_iff_of_mem_basicOpen ha ha (k := 1)
    (mul_one j).symm hx).1 h hx

include ha in
/-- **A homogeneous coordinate vanishes exactly off its basic open set.** If `Proj 𝒜` is covered
by basic open sets of homogeneous elements whose degrees divide `j` — which holds for instance
on a projective space — then the global section of `𝒪(j)` attached to `a ∈ 𝒜 j` vanishes at a
point exactly when that point lies outside `D₊(a)`.

Only the implication from `x ∉ D₊(a)` to vanishing uses the covering hypothesis; the converse is
`AlgebraicGeometry.Proj.not_vanishesAt_homogeneousSection_of_mem_basicOpen`, and at a single
point of a basic open set `D₊(f)` with `deg f` dividing `j` the pointwise form
`AlgebraicGeometry.Proj.vanishesAt_homogeneousSection_iff_of_mem_basicOpen` needs no covering
condition. -/
theorem vanishesAt_homogeneousSection_iff (H : IsCoveredByDvdDegree 𝒜 (j : ℤ)) (x : Proj 𝒜) :
    (twistingSheaf 𝒜 j).VanishesAt (homogeneousSection ha) x ↔ x ∉ Proj.basicOpen 𝒜 a := by
  obtain ⟨m, f, hf, hfx, hmj⟩ := H x
  obtain ⟨k, hk⟩ := Int.natCast_dvd_natCast.1 hmj
  exact vanishesAt_homogeneousSection_iff_of_mem_basicOpen ha hf hk hfx

include ha in
/-- **The non-vanishing locus of a homogeneous coordinate is its basic open set.** For `a` of
positive degree that locus is therefore an affine open subset of `Proj 𝒜`, by
`AlgebraicGeometry.Proj.isAffineOpen_basicOpen`. -/
theorem setOf_not_vanishesAt_homogeneousSection (H : IsCoveredByDvdDegree 𝒜 (j : ℤ)) :
    {x : Proj 𝒜 | ¬ (twistingSheaf 𝒜 j).VanishesAt (homogeneousSection ha) x} =
      (Proj.basicOpen 𝒜 a : Set (Proj 𝒜)) :=
  Set.ext fun x ↦ by simp [vanishesAt_homogeneousSection_iff ha H x]

end Vanishing

section MvPolynomial

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (τ B : Type u) [CommRing B]

/-- **On a projective space a homogeneous coordinate vanishes exactly off its basic open set.**
On `Proj B[Xᵢ]`, the projective space over the affine base `Spec B` with homogeneous coordinates
indexed by `τ`, the covering hypothesis of
`AlgebraicGeometry.Proj.vanishesAt_homogeneousSection_iff` is automatic: the irrelevant ideal of
the total-degree grading is generated by the variables, which are homogeneous of degree one. -/
theorem vanishesAt_homogeneousSection_homogeneousSubmodule_iff {j : ℕ} {a : MvPolynomial τ B}
    (ha : a ∈ homogeneousSubmodule τ B j) (x : Proj (homogeneousSubmodule τ B)) :
    (twistingSheaf (homogeneousSubmodule τ B) j).VanishesAt (homogeneousSection ha) x ↔
      x ∉ Proj.basicOpen (homogeneousSubmodule τ B) a :=
  vanishesAt_homogeneousSection_iff ha (isCoveredByDvdDegree_of_irrelevant_le_span
    (g := (X : τ → MvPolynomial τ B)) (n := fun _ ↦ 1) (fun i ↦ isHomogeneous_X B i)
    (irrelevant_le_idealOfVars τ B) (fun _ ↦ one_dvd (j : ℤ))) x

end MvPolynomial

end Proj

end AlgebraicGeometry
