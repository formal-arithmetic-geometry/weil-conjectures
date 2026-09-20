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
`D₊(a)`, which is an affine open subset of `Proj 𝒜`.

`WeilConjectures/AlgebraicGeometry/TwistingSheaf.lean` already describes the locus where the
*value* of `homogeneousSection ha` at a point `x` — an element of the localization `A_x` of the
whole graded ring, not of the local ring `𝒪_{Proj 𝒜, x}` of the scheme — is a unit
(`AlgebraicGeometry.Proj.isUnit_homogeneousSection_apply_iff`). What is proved here is the
scheme-theoretic form: the germ of the section at `x` lies in `𝔪ₓ 𝒪(j)ₓ` exactly when
`a ∈ x`. This is the form that the theory of invertible sheaves consumes, and the form that
pulls back along a morphism of schemes.

The translation between the two goes through a local trivialisation of `𝒪(j)`. If `f` is a
homogeneous element of degree `m` with `m * k = j` and `f ∉ x`, then `𝒪(j)` is free of rank one
on `f ^ k` over `D₊(f)` (`AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.sectionPowEquiv`),
so multiplication by `f ^ k` is an isomorphism `𝒪_{D₊(f)} ≅ 𝒪(j)|_{D₊(f)}` and
`AlgebraicGeometry.Scheme.Modules.vanishesAt_iff_notMem_basicOpen` applies: the section vanishes
at `x` exactly where its coefficient `a / f ^ k` does, and that coefficient is a unit of the
local ring exactly when `a ∉ x`. Such an `f` exists at every point of `Proj 𝒜` as soon as
`AlgebraicGeometry.Proj.IsCoveredByDvdDegree 𝒜 j` holds, which is the case for a polynomial
ring, and more generally whenever the irrelevant ideal is generated in degree one.

## Main results

- `AlgebraicGeometry.Proj.isIso_unitSmulRestrictHom_sectionPow`: over `D₊(f)`, multiplication by
  the tautological generator `f ^ k` is an isomorphism `𝒪_{D₊(f)} ≅ 𝒪(m * k)|_{D₊(f)}`.
- `AlgebraicGeometry.Proj.vanishesAt_homogeneousSection_iff_of_mem_basicOpen`: at a point of a
  basic open set `D₊(f)` with `deg f` dividing `j`, the section of `𝒪(j)` attached to `a ∈ 𝒜 j`
  vanishes exactly off `D₊(a)`.
- `AlgebraicGeometry.Proj.not_vanishesAt_homogeneousSection`: unconditionally, the section
  attached to `a` does not vanish at any point of `D₊(a)`.
- `AlgebraicGeometry.Proj.setOf_not_vanishesAt_homogeneousSection`: the non-vanishing locus of
  the section attached to `a` is `D₊(a)`, and
  `AlgebraicGeometry.Proj.exists_isAffineOpen_eq_setOf_not_vanishesAt` records that this locus
  is an affine open subset of `Proj 𝒜` when `a` has positive degree.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite TopologicalSpace TopCat

namespace AlgebraicGeometry

universe u

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

namespace Proj

open ProjectiveSpectrum.TwistingSheaf Scheme.Modules

section Trivialisation

variable {m : ℕ} {f : A} (hf : f ∈ 𝒜 m)

include hf in
/-- The tautological generator of `𝒪(m * k)` over an open set on which a homogeneous element `f`
of degree `m` is invertible restricts to the tautological generator over any smaller open set. -/
lemma map_sectionPow {U V : (Proj 𝒜).Opens} (hVU : V ≤ U)
    (hU : ∀ x : (op U).unop, f ∉ x.1.asHomogeneousIdeal.toIdeal)
    (hV : ∀ x : (op V).unop, f ∉ x.1.asHomogeneousIdeal.toIdeal) (k : ℤ) {c : ℤ}
    (hc : c = m * k) :
    (twistingSheaf 𝒜 c).presheaf.map (homOfLE hVU).op (sectionPow hf hU k hc) =
      sectionPow hf hV k hc :=
  Subtype.ext (funext fun _ ↦ rfl)

include hf in
/-- **Multiplication by the tautological generator is an isomorphism over a trivialising open
set.** If `f` is homogeneous of degree `m` and invertible on `W`, then multiplication by `f ^ k`
is an isomorphism `𝒪_W ≅ 𝒪(m * k)|_W` of sheaves of modules on the open subscheme `W`. -/
lemma isIso_unitSmulRestrictHom_sectionPow {W : (Proj 𝒜).Opens}
    (hW : ∀ x : (op W).unop, f ∉ x.1.asHomogeneousIdeal.toIdeal) (k : ℤ) {c : ℤ}
    (hc : c = m * k) :
    IsIso (unitSmulRestrictHom (M := twistingSheaf 𝒜 c) (W := W) (sectionPow hf hW k hc)) := by
  have hiso : IsIso (smulRestrictHom (M := twistingSheaf 𝒜 c) (W := W)
      (sectionPow hf hW k hc)) := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    have hle : W.ι ''ᵁ V ≤ W := W.ι_image_le V
    have hV : ∀ x : (op (W.ι ''ᵁ V)).unop, f ∉ x.1.asHomogeneousIdeal.toIdeal :=
      fun x ↦ hW ⟨x.1, hle x.2⟩
    have happ : ∀ r, (smulRestrictHom (M := twistingSheaf 𝒜 c) (W := W)
        (sectionPow hf hW k hc)).app V r = sectionPowEquiv hf hV k hc r := by
      intro r
      change smulSection (M := twistingSheaf 𝒜 c) (sectionPow hf hW k hc) _ hle r = _
      rw [smulSection]
      simp only [AddMonoidHom.mk'_apply, sectionPowEquiv_apply]
      rw [map_sectionPow hf hle hW hV k hc]
    have hbij := (sectionPowEquiv hf hV k hc).bijective
    refine ⟨fun r r' h ↦ hbij.1 ?_, fun t ↦ ?_⟩
    · rw [← happ, ← happ, h]
    · obtain ⟨r, hr⟩ := hbij.2 t
      exact ⟨r, by rw [happ, hr]⟩
  have hfac : unitSmulRestrictHom (M := twistingSheaf 𝒜 c) (W := W) (sectionPow hf hW k hc) =
      (restrictUnitIso W.ι).inv ≫
        smulRestrictHom (M := twistingSheaf 𝒜 c) (W := W) (sectionPow hf hW k hc) := rfl
  rw [hfac]
  infer_instance

end Trivialisation

section Vanishing

variable {j : ℕ} {a : A} (ha : a ∈ 𝒜 j)

include ha in
/-- **A homogeneous element vanishes, as a section of `𝒪(j)`, exactly off its basic open set.**
At a point `x` of a basic open set `D₊(f)` with `f` homogeneous of degree `m` and `j = m * k`,
the global section of `𝒪(j)` attached to `a ∈ 𝒜 j` vanishes if and only if `x ∉ D₊(a)`. -/
theorem vanishesAt_homogeneousSection_iff_of_mem_basicOpen {m : ℕ} {f : A} (hf : f ∈ 𝒜 m)
    {k : ℕ} (hjk : j = m * k) {x : Proj 𝒜} (hx : x ∈ Proj.basicOpen 𝒜 f) :
    (twistingSheaf 𝒜 j).VanishesAt (homogeneousSection ha) x ↔ x ∉ Proj.basicOpen 𝒜 a := by
  have hc : (j : ℤ) = m * (k : ℤ) := by exact_mod_cast hjk
  have hW : ∀ y : (op (Proj.basicOpen 𝒜 f)).unop, f ∉ y.1.asHomogeneousIdeal.toIdeal :=
    fun y ↦ y.2
  set W : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 f with hWdef
  set g : Γ(twistingSheaf 𝒜 j, W) := sectionPow hf hW (k : ℤ) hc with hgdef
  have : IsIso (unitSmulRestrictHom g) := isIso_unitSmulRestrictHom_sectionPow hf hW (k : ℤ) hc
  set r : Γ(Proj 𝒜, W) :=
    powCoeff hf hW (k : ℤ) hc
      ((twistingSheaf 𝒜 j).presheaf.map W.leTop.op (homogeneousSection ha)) with hrdef
  have hres : (twistingSheaf 𝒜 j).presheaf.map W.leTop.op (homogeneousSection ha) = r • g :=
    (powCoeff_smul_sectionPow hf hW (k : ℤ) hc _).symm
  rw [vanishesAt_iff_notMem_basicOpen g (homogeneousSection ha) r hres hx]
  -- it remains to identify the basic open set of the coefficient `a / f ^ k` with `D₊(a)`
  have hfk : f ^ k ∉ x.asHomogeneousIdeal := fun h ↦ hx (x.isPrime.mem_of_pow_mem k h)
  have hfkd : f ^ k ∈ 𝒜 j := by
    rw [hjk, mul_comm]
    simpa [smul_eq_mul] using SetLike.pow_mem_graded k hf
  have hval : r.1 ⟨x, hx⟩ =
      (HomogeneousLocalization.mk ⟨j, ⟨a, ha⟩, ⟨f ^ k, hfkd⟩, hfk⟩ :
        HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) := by
    have hsx : ((twistingSheaf 𝒜 j).presheaf.map W.leTop.op (homogeneousSection ha)).1
        ⟨x, hx⟩ = Localization.mk a 1 := rfl
    refine HomogeneousLocalization.val_injective _ ?_
    rw [hrdef, val_powCoeff, HomogeneousLocalization.val_mk,
      powFun_neg_natCast hW k ⟨x, hx⟩ hfk, hsx]
    simp [Localization.mk_mul]
  have hgerm : Proj.stalkIso' 𝒜 x ((Proj 𝒜).presheaf.germ W x hx r) = r.1 ⟨x, hx⟩ :=
    Proj.stalkIso'_germ 𝒜 W x hx r
  refine not_congr ?_
  rw [Scheme.mem_basicOpen _ r x hx, ← isUnit_mk_iff_mem_basicOpen ha x hfkd hfk, ← hval, ← hgerm]
  exact ⟨fun h ↦ h.map (Proj.stalkIso' 𝒜 x), fun h ↦ by
    simpa using h.map (Proj.stalkIso' 𝒜 x).symm⟩

include ha in
/-- **A homogeneous element does not vanish, as a section of `𝒪(j)`, on its own basic open
set.** Unlike
`AlgebraicGeometry.Proj.vanishesAt_homogeneousSection_iff_of_mem_basicOpen`, this direction
needs no auxiliary trivialising element: `a` itself trivialises `𝒪(j)` on `D₊(a)`. -/
theorem not_vanishesAt_homogeneousSection {x : Proj 𝒜} (hx : x ∈ Proj.basicOpen 𝒜 a) :
    ¬ (twistingSheaf 𝒜 j).VanishesAt (homogeneousSection ha) x := fun h ↦
  (vanishesAt_homogeneousSection_iff_of_mem_basicOpen ha ha (k := 1)
    (mul_one j).symm hx).1 h hx

include ha in
/-- **A homogeneous coordinate vanishes exactly off its basic open set.** If `Proj 𝒜` is covered
by basic open sets of homogeneous elements whose degrees divide `j` — which holds for instance
on a projective space — then the global section of `𝒪(j)` attached to `a ∈ 𝒜 j` vanishes at a
point exactly when that point lies outside `D₊(a)`. -/
theorem vanishesAt_homogeneousSection_iff (H : IsCoveredByDvdDegree 𝒜 (j : ℤ)) (x : Proj 𝒜) :
    (twistingSheaf 𝒜 j).VanishesAt (homogeneousSection ha) x ↔ x ∉ Proj.basicOpen 𝒜 a := by
  obtain ⟨m, f, hf, hfx, hmj⟩ := H x
  obtain ⟨k, hk⟩ := Int.natCast_dvd_natCast.1 hmj
  exact vanishesAt_homogeneousSection_iff_of_mem_basicOpen ha hf hk hfx

include ha in
/-- **The non-vanishing locus of a homogeneous coordinate is its basic open set.** -/
theorem setOf_not_vanishesAt_homogeneousSection (H : IsCoveredByDvdDegree 𝒜 (j : ℤ)) :
    {x : Proj 𝒜 | ¬ (twistingSheaf 𝒜 j).VanishesAt (homogeneousSection ha) x} =
      (Proj.basicOpen 𝒜 a : Set (Proj 𝒜)) :=
  Set.ext fun x ↦ by simp [vanishesAt_homogeneousSection_iff ha H x]

include ha in
/-- **A homogeneous coordinate of positive degree does not vanish exactly on an affine open
subset of `Proj 𝒜`.** The locus is the basic open set `D₊(a)`, which is affine by
`AlgebraicGeometry.Proj.isAffineOpen_basicOpen`. -/
theorem exists_isAffineOpen_eq_setOf_not_vanishesAt (hj : 0 < j)
    (H : IsCoveredByDvdDegree 𝒜 (j : ℤ)) :
    ∃ U : (Proj 𝒜).Opens, IsAffineOpen U ∧
      (U : Set (Proj 𝒜)) =
        {x : Proj 𝒜 | ¬ (twistingSheaf 𝒜 j).VanishesAt (homogeneousSection ha) x} :=
  ⟨Proj.basicOpen 𝒜 a, Proj.isAffineOpen_basicOpen 𝒜 a ha hj,
    (setOf_not_vanishesAt_homogeneousSection ha H).symm⟩

end Vanishing

end Proj

end AlgebraicGeometry
