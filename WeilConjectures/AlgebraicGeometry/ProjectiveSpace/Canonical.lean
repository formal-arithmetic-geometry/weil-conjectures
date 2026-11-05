/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGeneratorIso
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartPolynomial
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistGenerator
public import WeilConjectures.LinearAlgebra.ExteriorPower.ChartTransition
public import WeilConjectures.RingTheory.Kaehler.LocalizationPolynomial

/-!
# The canonical sheaf of projective space

Let `A` be a commutative ring and `ℙ = ℙ(n; Spec A)` with `Nat.card n = d + 1`. The canonical
sheaf `ω_ℙ = ⋀ᵈ Ω¹_{ℙ/A}` is invertible, with free generator
`ηᵢ = (-1)ⁱ ⋀_{k ≠ i} d(x_k / xᵢ)` on the standard open `Uᵢ = D₊(xᵢ)`, and `ω_ℙ ≅ 𝒪(-d-1)`,
`ηᵢ ↦ eᵢ^{(-d-1)}`. The signs and the order of the wedge products refer to an enumeration
`e : n ≃ Fin (d + 1)`.

## Main declarations

- `AlgebraicGeometry.ProjectiveSpace.canonicalModule`: `ω_ℙ = ⋀ᵈ Ω¹_{ℙ/S}`.
- `AlgebraicGeometry.ProjectiveSpace.canonicalGenerator`: the local generator `ηᵢ` on `Uᵢ`, a
  free generator by `isFreeGenerator_canonicalGenerator`.
- `AlgebraicGeometry.ProjectiveSpace.map_canonicalGenerator_eq_transitionUnit_smul`: the
  transition rule `ηᵢ = (xᵢ / xⱼ)^{-(d+1)} ηⱼ` on `Uᵢ ∩ Uⱼ`.
- `AlgebraicGeometry.ProjectiveSpace.canonicalModuleIsoTwist`: `ω_ℙ ≅ 𝒪(-d-1)`, `ηᵢ ↦ eᵢ^{(-d-1)}`.

(blueprint: `lem-pc-projective-space-canonical`)
-/

@[expose] public section

universe u

open CategoryTheory Opposite MvPolynomial Module

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules

variable (n : Type u) (A : Type u) [CommRing A]

/-! ### The ratios of homogeneous coordinates on the overlaps of the standard opens -/

section Ratio

open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n} {S : Scheme.{u}}

lemma val_awayMap_awayXRatio {i k : n} {e : ℕ} {g : MvPolynomial n (ULift.{u} ℤ)}
    (hg : g ∈ homogeneousSubmodule n (ULift.{u} ℤ) e) {x : MvPolynomial n (ULift.{u} ℤ)}
    (hx : x = X i * g) :
    (awayMap _ hg hx (awayXRatio (ULift.{u} ℤ) i k)).val =
      Localization.mk (X k * g) ⟨x, Submonoid.mem_powers x⟩ := by
  rw [awayXRatio, awayMap_mk, Away.val_mk]
  simp

/-- The restriction of `x_k / xᵢ` to an open contained in the preimage of `D₊(x)`, for a
multiple `x = Tᵢ g` of `Tᵢ`, computed in the degree-zero part of `ℤ[T]ₓ`. -/
lemma map_coordRatio {i k : n} {e : ℕ} {g : MvPolynomial n (ULift.{u} ℤ)}
    (hg : g ∈ homogeneousSubmodule n (ULift.{u} ℤ) e) {x : MvPolynomial n (ULift.{u} ℤ)}
    (hx : x = X i * g) {W : ℙ(n; S).Opens}
    (hW : W ≤ toProjInt n S ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) x)
    (hW' : W ≤ standardOpen n S i) :
    ℙ(n; S).presheaf.map (homOfLE hW').op (coordRatio n S i k) =
      (Proj.awayToSection _ x ≫ (toProjInt n S).appLE _ W hW)
        (awayMap _ hg hx (awayXRatio (ULift.{u} ℤ) i k)) := by
  have key : Proj.awayToSection _ (X i) ≫ (toProjInt n S).app _ ≫
      ℙ(n; S).presheaf.map (homOfLE hW').op =
      CommRingCat.ofHom (awayMap _ hg hx) ≫ Proj.awayToSection _ x ≫
        (toProjInt n S).appLE _ W hW := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Proj.awayMap_awayToSection_assoc,
      Scheme.Hom.map_appLE]
  have := ConcreteCategory.congr_hom key (awayXRatio (ULift.{u} ℤ) i k)
  simp only [CategoryTheory.comp_apply] at this ⊢
  exact this

@[simp]
lemma coordRatio_self (i : n) : coordRatio n S i i = 1 := by
  rw [coordRatio, awayXRatio_self, map_one, map_one]

/-- **The change of affine coordinates** `x_k / xᵢ = (x_k / xⱼ) (xⱼ / xᵢ)` on an open contained
in `Uᵢ ∩ Uⱼ`. -/
lemma map_coordRatio_eq_mul {i j : n} {W : ℙ(n; S).Opens} (hi : W ≤ standardOpen n S i)
    (hj : W ≤ standardOpen n S j) (k : n) :
    ℙ(n; S).presheaf.map (homOfLE hi).op (coordRatio n S i k) =
      ℙ(n; S).presheaf.map (homOfLE hj).op (coordRatio n S j k) *
        ℙ(n; S).presheaf.map (homOfLE hi).op (coordRatio n S i j) := by
  have hXi := X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i
  have hXj := X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) (σ := n) j
  have hW := (le_inf hi hj).trans (standardOpen_inf_le (S := S) i j)
  rw [map_coordRatio hXj (x := X i * X j) rfl hW,
    map_coordRatio hXi (x := X i * X j) (by ring) hW,
    map_coordRatio hXj (x := X i * X j) rfl hW, ← map_mul]
  refine appLE_awayToSection_congr _ ?_
  rw [val_mul, val_awayMap_awayXRatio, val_awayMap_awayXRatio, val_awayMap_awayXRatio,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

end Ratio

/-! ### The canonical module and its local generators -/

variable (S : Scheme.{u}) (d : ℕ)

variable {n S d} (e : n ≃ Fin (d + 1))

end AlgebraicGeometry.ProjectiveSpace
