/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistTensor

/-!
# The transition rule of the twisting sheaves on projective space

The twisting sheaf `𝒪(d)` on `ℙ(n; S)` has the free generator `eᵢ^{(d)} = xᵢᵈ` on the standard
open `Uᵢ = D₊(xᵢ)` (`AlgebraicGeometry.ProjectiveSpace.twistGenerator`), and on `Uᵢ ∩ Uⱼ` these
generators are related by the transition units `u_{ij} = (xᵢ / xⱼ)ᵈ`
(`AlgebraicGeometry.ProjectiveSpace.transitionUnit`):
`eᵢ^{(d)} = u_{ij} eⱼ^{(d)}` (`AlgebraicGeometry.ProjectiveSpace.twistGenerator_map_eq_smul`).

As a consequence, `𝒪(d)` with the generators `e₀^{(d)}`, `e₁^{(d)}` is a twisted structure
sheaf on `ℙ¹_S` in the sense of `AlgebraicGeometry.ProjectiveLine.TwistData`
(`AlgebraicGeometry.ProjectiveLine.twistData`).
-/

@[expose] public section

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization

noncomputable section

namespace Localization

variable {R : Type*} [CommRing R] {M : Submonoid R}

/-- `fᵈ⁺ / fᵈ⁻ = (f / 1)ᵈ` in a localization in which `f` becomes a unit. -/
lemma mk_pow_toNat_eq_val_zpow {f : R} (hf : IsUnit (algebraMap R (Localization M) f)) (d : ℤ)
    (h : f ^ (-d).toNat ∈ M) :
    Localization.mk (f ^ d.toNat) ⟨f ^ (-d).toNat, h⟩ =
      ((hf.unit ^ d : (Localization M)ˣ) : Localization M) := by
  set F := hf.unit
  have hF : algebraMap R (Localization M) f = F := hf.unit_spec.symm
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul, map_pow, map_pow,
    hF, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
    ← zpow_natCast, ← zpow_natCast, ← zpow_add]
  congr 2
  omega

end Localization

namespace AlgebraicGeometry

namespace Proj

open ProjectiveSpectrum.Twist

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- Evaluation at a point `x ∈ W` of the sections of the structure sheaf of `Proj 𝒜` over `W`,
as a ring homomorphism to the localization at `x`. -/
def evalAt {W : (Proj 𝒜).Opens} (x : W) :
    Γ(Proj 𝒜, W) →+* Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal where
  toFun s := (s.1 x).val
  map_one' := val_one
  map_mul' _ _ := val_mul _ _
  map_zero' := val_zero
  map_add' _ _ := val_add _ _

lemma evalAt_apply {W : (Proj 𝒜).Opens} (x : W) (s : Γ(Proj 𝒜, W)) :
    evalAt x s = (s.1 x).val :=
  rfl

/-- Sections of the structure sheaf of `Proj 𝒜` are determined by their values. -/
lemma section_ext {W : (Proj 𝒜).Opens} {s t : Γ(Proj 𝒜, W)}
    (h : ∀ x : W, evalAt x s = evalAt x t) : s = t :=
  Subtype.ext (funext fun x ↦ val_injective _ (h x))

lemma evalAt_map {V W : (Proj 𝒜).Opens} (h : W ≤ V) (s : Γ(Proj 𝒜, V)) (x : W) :
    evalAt x ((Proj 𝒜).presheaf.map (homOfLE h).op s) = evalAt ⟨x.1, h x.2⟩ s :=
  rfl

variable {f g : A}

/-- **The transition rule for the sections `fᵈ`**: if `u` is a unit over an open
`W ⊆ D₊(f) ∩ D₊(g)` (`f`, `g` of degree `1`) with `u g = f` at every point of `W`, i.e.
`u = f / g`, then `fᵈ = uᵈ • gᵈ` on `W` for every `d : ℤ`. -/
lemma twistPowSection_map_eq_zpow_smul (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) {W : (Proj 𝒜).Opens}
    (hWf : W ≤ Proj.basicOpen 𝒜 f) (hWg : W ≤ Proj.basicOpen 𝒜 g) (u : Γ(Proj 𝒜, W)ˣ)
    (hu : ∀ x : W, evalAt x u * algebraMap A _ g = algebraMap A _ f) (d : ℤ) :
    ((u ^ d : Γ(Proj 𝒜, W)ˣ) : Γ(Proj 𝒜, W)) •
        (twist 𝒜 d).presheaf.map (homOfLE hWg).op (twistPowSection d hg) =
      (twist 𝒜 d).presheaf.map (homOfLE hWf).op (twistPowSection d hf) := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  have hfx := IsLocalization.map_units (Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)
    (⟨f, by simpa using pow_mem_primeCompl ⟨x.1, hWf x.2⟩ 1⟩ :
      x.1.asHomogeneousIdeal.toIdeal.primeCompl)
  have hgx := IsLocalization.map_units (Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)
    (⟨g, by simpa using pow_mem_primeCompl ⟨x.1, hWg x.2⟩ 1⟩ :
      x.1.asHomogeneousIdeal.toIdeal.primeCompl)
  have hv : Units.map (evalAt x).toMonoidHom u * hgx.unit = hfx.unit :=
    Units.ext (hu x)
  have key : evalAt x ((u ^ d : Γ(Proj 𝒜, W)ˣ) : Γ(Proj 𝒜, W)) *
      ((twistPowSection d hg).1 ⟨x.1, hWg x.2⟩ :
        Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      ((twistPowSection d hf).1 ⟨x.1, hWf x.2⟩ :
        Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) := by
    rw [val_twistPowSection_apply, val_twistPowSection_apply,
      Localization.mk_pow_toNat_eq_val_zpow hgx, Localization.mk_pow_toNat_eq_val_zpow hfx,
      ← hv, mul_zpow, Units.val_mul, ← map_zpow]
    rfl
  exact key

end Proj

namespace ProjectiveSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u) (S : Scheme.{u})

/-- The value of the section `Tᵢ / Tⱼ` of the integral model at a point of `D₊(Tⱼ)`:
`(Tᵢ / Tⱼ) Tⱼ = Tᵢ`. -/
lemma evalAt_awayToSection_awayRatio_mul (i j : n)
    (x : Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X j)) :
    Proj.evalAt x (Proj.awayToSection _ (X j) (awayRatio n i j)) *
        algebraMap (MvPolynomial n (ULift.{u} ℤ))
          (Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) (X j) =
      algebraMap _ _ (X i : MvPolynomial n (ULift.{u} ℤ)) := by
  have h := ProjectiveSpectrum.Proj.awayToSection_apply (homogeneousSubmodule n (ULift.{u} ℤ))
    (X j) (awayRatio n i j) x
  rw [Proj.evalAt_apply]
  erw [h]
  rw [awayRatio, Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk', RingHom.id_apply]
  convert IsLocalization.mk'_spec (Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)
    (X i : MvPolynomial n (ULift.{u} ℤ)) _ using 2
  simp

/-- `Tᵢ / Tⱼ` restricted to an open `W ⊆ D₊(Tⱼ)`: `(Tᵢ / Tⱼ) Tⱼ = Tᵢ` at every point of `W`. -/
lemma evalAt_map_awayToSection_awayRatio_mul (i j : n)
    {W : (Proj (homogeneousSubmodule n (ULift.{u} ℤ))).Opens}
    (hW : W ≤ Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X j)) (x : W) :
    Proj.evalAt x ((Proj (homogeneousSubmodule n (ULift.{u} ℤ))).presheaf.map (homOfLE hW).op
        (Proj.awayToSection _ (X j) (awayRatio n i j))) *
        algebraMap (MvPolynomial n (ULift.{u} ℤ))
          (Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) (X j) =
      algebraMap _ _ (X i : MvPolynomial n (ULift.{u} ℤ)) :=
  evalAt_awayToSection_awayRatio_mul n i j ⟨x.1, hW x.2⟩


/-- `X i * X j` is a unit at every point of `D₊(Tᵢ) ∩ D₊(Tⱼ)`. -/
lemma isUnit_algebraMap_X_mul_X (i j : n)
    (x : (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i) ⊓
      Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X j) :
        (Proj (homogeneousSubmodule n (ULift.{u} ℤ))).Opens)) :
    IsUnit (algebraMap (MvPolynomial n (ULift.{u} ℤ))
      (Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) (X i * X j)) :=
  IsLocalization.map_units (Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)
    (⟨X i * X j, by simpa using Proj.pow_mem_primeCompl (𝒜 := homogeneousSubmodule n
      (ULift.{u} ℤ)) (f := X i * X j) ⟨x.1, by rw [Proj.basicOpen_mul]; exact x.2⟩ 1⟩ :
      x.1.asHomogeneousIdeal.toIdeal.primeCompl)

/-- **The unit `Tᵢ / Tⱼ`** on `D₊(Tᵢ) ∩ D₊(Tⱼ)` in the integral model `Proj ℤ[T]`, with inverse
`Tⱼ / Tᵢ`. -/
def ratioUnitInt (i j : n) :
    Γ(Proj (homogeneousSubmodule n (ULift.{u} ℤ)),
      Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i) ⊓
        Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X j))ˣ where
  val := (Proj (homogeneousSubmodule n (ULift.{u} ℤ))).presheaf.map (homOfLE inf_le_right).op
    (Proj.awayToSection _ (X j) (awayRatio n i j))
  inv := (Proj (homogeneousSubmodule n (ULift.{u} ℤ))).presheaf.map (homOfLE inf_le_left).op
    (Proj.awayToSection _ (X i) (awayRatio n j i))
  val_inv := Proj.section_ext fun x ↦ (isUnit_algebraMap_X_mul_X n i j x).mul_right_cancel (by
    have h₁ := evalAt_map_awayToSection_awayRatio_mul n i j inf_le_right x
    have h₂ := evalAt_map_awayToSection_awayRatio_mul n j i inf_le_left x
    rw [map_mul, map_one, map_mul]
    linear_combination (Proj.evalAt x ((Proj (homogeneousSubmodule n (ULift.{u} ℤ))).presheaf.map
        (homOfLE inf_le_left).op (Proj.awayToSection _ (X i) (awayRatio n j i))) *
      algebraMap _ (Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)
        (X i : MvPolynomial n (ULift.{u} ℤ))) * h₁ +
      algebraMap _ (Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)
        (X i : MvPolynomial n (ULift.{u} ℤ)) * h₂)
  inv_val := Proj.section_ext fun x ↦ (isUnit_algebraMap_X_mul_X n i j x).mul_right_cancel (by
    have h₁ := evalAt_map_awayToSection_awayRatio_mul n i j inf_le_right x
    have h₂ := evalAt_map_awayToSection_awayRatio_mul n j i inf_le_left x
    rw [map_mul, map_one, map_mul]
    linear_combination (Proj.evalAt x ((Proj (homogeneousSubmodule n (ULift.{u} ℤ))).presheaf.map
        (homOfLE inf_le_left).op (Proj.awayToSection _ (X i) (awayRatio n j i))) *
      algebraMap _ (Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)
        (X i : MvPolynomial n (ULift.{u} ℤ))) * h₁ +
      algebraMap _ (Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)
        (X i : MvPolynomial n (ULift.{u} ℤ)) * h₂)

/-- **The transition rule of the twisting sheaves**: on the overlap `Uᵢ ∩ Uⱼ` of two standard
opens of `ℙ(n; S)`, the free generators `eᵢ^{(d)} = xᵢᵈ` and `eⱼ^{(d)} = xⱼᵈ` of `𝒪(d)`
satisfy `eᵢ^{(d)} = (xᵢ / xⱼ)ᵈ eⱼ^{(d)} = u_{ij} eⱼ^{(d)}` for the transition unit `u_{ij}` of
`transitionUnit`.

(blueprint: `def-pc-projective-space-twist`) -/
theorem twistGenerator_map_eq_smul (d : ℤ) (i j : n) :
    (twist n S d).presheaf.map (homOfLE inf_le_left).op (twistGenerator n S d i) =
      (transitionUnit n S d i j).1 •
        (twist n S d).presheaf.map (homOfLE inf_le_right).op (twistGenerator n S d j) := by
  have hXi := X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) (σ := n) i
  have hXj := X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) (σ := n) j
  have H := Proj.twistPowSection_map_eq_zpow_smul hXi hXj inf_le_left inf_le_right
    (ratioUnitInt n i j) (fun x ↦ evalAt_awayToSection_awayRatio_mul n i j ⟨x.1, x.2.2⟩) d
  have hW : standardOpen n S i ⊓ standardOpen n S j ≤ toProjInt n S ⁻¹ᵁ
      (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i) ⊓
        Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X j)) := fun _ hx ↦ hx
  have H' := pullbackSection_smul_map_eq (toProjInt n S) inf_le_left inf_le_right H hW
  let φ := ((toProjInt n S).app _ ≫ ℙ(n; S).presheaf.map (homOfLE hW).op).hom
  have hu : Units.map φ.toMonoidHom (ratioUnitInt n i j) = ratioUnit n S i j := by
    have key : Proj.awayToSection _ (X j) ≫
        (Proj (homogeneousSubmodule n (ULift.{u} ℤ))).presheaf.map (homOfLE inf_le_right).op ≫
          (toProjInt n S).app _ ≫ ℙ(n; S).presheaf.map (homOfLE hW).op =
        Proj.awayToSection _ (X j) ≫ (toProjInt n S).appLE _
          (standardOpen n S i ⊓ standardOpen n S j) inf_le_right := by
      rw [Scheme.Hom.naturality_assoc, ← Functor.map_comp, Scheme.Hom.appLE]
      rfl
    have k2 := ConcreteCategory.congr_hom key (awayRatio n i j)
    refine Units.ext ?_
    simp only [CategoryTheory.comp_apply] at k2
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, φ, ratioUnitInt,
      ratioUnit, ratio, CategoryTheory.comp_apply]
    exact k2
  have hc : (transitionUnit n S d i j).1 =
      ℙ(n; S).presheaf.map (homOfLE hW).op
        ((toProjInt n S).app _ (ratioUnitInt n i j ^ d).1) := by
    rw [transitionUnit, ← hu, ← map_zpow]
    rfl
  rw [hc]
  exact H'.symm

end ProjectiveSpace

namespace ProjectiveLine

open ProjectiveSpace

variable (S : Scheme.{u})

/-- **`𝒪(d)` is a twisted structure sheaf on `ℙ¹_S`**: the twisting sheaf `𝒪(d)` of
`ProjectiveSpace.twist`, with the generators `g₀ = x₀ᵈ` over `U₀` and `g₁ = x₁ᵈ` over `U₁`
(`ProjectiveSpace.twistGenerator`), which satisfy the glueing relation
`g₀ = (x₀ / x₁)ᵈ g₁ = t^{-d} g₁` by `ProjectiveSpace.twistGenerator_map_eq_smul`.

(blueprint: `def-sc-p1-standard`) -/
def twistData (d : ℤ) : TwistData S d (twist (ULift.{u} (Fin 2)) S d) where
  g₀ := twistGenerator (ULift.{u} (Fin 2)) S d ⟨0⟩
  g₁ := twistGenerator (ULift.{u} (Fin 2)) S d ⟨1⟩
  bijective_smul_g₀ V hV := isFreeGenerator_twistGenerator (ULift.{u} (Fin 2)) S d ⟨0⟩ V hV
  bijective_smul_g₁ V hV := isFreeGenerator_twistGenerator (ULift.{u} (Fin 2)) S d ⟨1⟩ V hV
  map_g₀ := twistGenerator_map_eq_smul (ULift.{u} (Fin 2)) S d ⟨0⟩ ⟨1⟩

end ProjectiveLine

end AlgebraicGeometry
