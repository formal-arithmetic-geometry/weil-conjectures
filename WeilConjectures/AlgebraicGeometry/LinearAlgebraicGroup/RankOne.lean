/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy
public import WeilConjectures.GroupTheory.WeilGroup
public import WeilConjectures.Mathlib.GroupTheory.Exponent
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Rank-one characters of degree data

Let `(W, deg, γ)` be a degree datum with degree-zero subgroup `P`, and let `χ : W → A` be a
character with values in a commutative group, such as the unit group `Eˣ` of a field. Put
`z = χ γ`. The *finite part* `χ_fin : w ↦ χ w * z ^ (-deg w)` of `χ` is again a character, it is
trivial on `γ`, its image is exactly `χ (P)`, and `χ = χ_fin * χ_z` with `χ_z : w ↦ z ^ deg w`.
This is the factorization of `sk-p-rankone`, read on the degree datum itself rather than on its
presentation `P ⋊ ℤ` as a split cyclic extension (`SemidirectProduct.finitePart`).

Applied to the Weil group `W(X₀) = π₁(X₀) ×_{Gal(k / k₀)} ℤ` (`MonoidHom.weilGroup`) with a lift
`s` of the geometric Frobenius, it says that a rank-one character with finite geometric image is
a character of finite order times the unramified character `w ↦ χ(s) ^ deg w`.

For a rank-one representation `ρ = χ : W → GL₁` with finite geometric image `A = χ(P)`, the
geometric monodromy group is `A` itself, the arithmetic monodromy extension is the direct
product `A × ℤ`, and the map to matrices is `(a, m) ↦ a cᵐ` with `c = χ(γ)`.

## Main declarations

* `AlgebraicGeometry.Monodromy.DegreeDatum.finitePart`: the finite part of a character.
* `AlgebraicGeometry.Monodromy.DegreeDatum.ofWeilGroup`: the degree datum of a Weil group with a
  lift of the Frobenius.
* `AlgebraicGeometry.Monodromy.DegreeDatum.finitePart_ofWeilGroup`: the finite-order part times a
  degree character, for the Weil group.
* `AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.arithmeticMonodromyExtensionEquivProd`: the
  arithmetic monodromy extension `A × ℤ` of a rank-one representation with finite geometric
  image `A`.

## Blueprint

`AlgebraicGeometry.Monodromy.DegreeDatum.finitePart_ofWeilGroup` implements
`cor-wf-rank-one-degree-factorization-curve`;
`RepresentedDegreeDatum.arithmeticMonodromyExtensionEquivProd`, with the formula `j(a, m) = a cᵐ`
in `arithmeticMonodromyExtensionHom_arithmeticMonodromyExtensionEquivProd_symm`, implements
`lem-wf-rank-one-algebraic-extension`.

The factorization of `sk-p-rankone` itself is `SemidirectProduct.eq_finitePart_mul_degreeCharacter`
and its companions, stated on the presentation `P ⋊ ℤ`. The `DegreeDatum` versions in this file
are the same statements for an abstract degree datum, which is the form needed for the Weil
group; they are proved directly, since `DegreeDatum` is not available in the `Mathlib` mirror
file where the `SemidirectProduct` versions live.

`MonoidHom.weilGroup` is the concrete fibre product `G ×_Γ ℤ`. It is not related here to the
abstract Weil group `AlgebraicGeometry.WeilGroup` of
`WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic`, which takes a topological group with
a surjective degree map to `ℤ` as data attached to a curve; `MonoidHom.weilGroup` with
`MonoidHom.weilGroupDeg` constructs the underlying group and degree map from a fundamental group
and its Frobenius, as in `AlgebraicGeometry.Scheme.FiniteEtale.weilGroup`.
-/

@[expose] public section

open Matrix.GeneralLinearGroup

namespace AlgebraicGeometry.Monodromy

namespace DegreeDatum

variable {W : Type*} [Group W] (D : DegreeDatum W) {A : Type*} [CommGroup A]

/-- The character `χ_z : w ↦ z ^ deg w` attached to `z : A`. -/
def degreeCharacter (z : A) : W →* A :=
  (zpowersHom A z).comp D.deg

@[simp]
theorem degreeCharacter_apply (z : A) (w : W) : D.degreeCharacter z w = z ^ (D.deg w).toAdd :=
  rfl

/-- The finite part `χ_fin = χ / χ_z` of a character `χ`, where `z = χ γ`; explicitly
`χ_fin w = χ w * z ^ (-deg w)`. -/
def finitePart (χ : W →* A) : W →* A :=
  χ / D.degreeCharacter (χ D.degreeOneElement)

variable (χ : W →* A)

theorem finitePart_apply (w : W) :
    D.finitePart χ w = χ w / χ D.degreeOneElement ^ (D.deg w).toAdd :=
  rfl

theorem eq_finitePart_mul_degreeCharacter :
    χ = D.finitePart χ * D.degreeCharacter (χ D.degreeOneElement) :=
  (div_mul_cancel χ _).symm

@[simp]
theorem finitePart_degreeOneElement : D.finitePart χ D.degreeOneElement = 1 := by
  simp [finitePart_apply, D.deg_degreeOneElement]

theorem finitePart_of_mem_ker {u : W} (hu : u ∈ D.deg.ker) : D.finitePart χ u = χ u := by
  rw [finitePart_apply, MonoidHom.mem_ker.1 hu, toAdd_one, zpow_zero, div_one]

/-- The image of the finite part is the image of `χ` on the degree-zero subgroup: every `w` is
`g γⁿ` with `n = deg w` and `g` of degree zero, and `χ_fin (g γⁿ) = χ g`. -/
theorem range_finitePart : Set.range (D.finitePart χ) = χ '' D.deg.ker := by
  ext a
  constructor
  · rintro ⟨w, rfl⟩
    set m := (D.deg w).toAdd
    have hg : w * (D.degreeOneElement ^ m)⁻¹ ∈ D.deg.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, D.deg_degreeOneElement, ← ofAdd_zsmul,
        smul_eq_mul, mul_one, ofAdd_toAdd, mul_inv_cancel]
    refine ⟨_, hg, ?_⟩
    rw [← D.finitePart_of_mem_ker χ hg, map_mul, map_inv, map_zpow, finitePart_degreeOneElement,
      one_zpow, inv_one, mul_one]
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, D.finitePart_of_mem_ker χ hu⟩

section WeilGroup

variable {G Γ : Type*} [Group G] [Group Γ] (π : G →* Γ) (Φ : Γ)

/-- The degree datum `(W(π, Φ), deg, s)` of a Weil group with an element `s` of degree one. -/
def ofWeilGroup (s : π.weilGroup Φ) (hs : π.weilGroupDeg Φ s = Multiplicative.ofAdd 1) :
    DegreeDatum (π.weilGroup Φ) where
  deg := π.weilGroupDeg Φ
  surjective_deg m := ⟨s ^ m.toAdd, by
    rw [map_zpow, hs, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]⟩
  degreeOneElement := s
  deg_degreeOneElement := hs

/-- **Finite-order part times a degree character.** Let `W = W(π, Φ)` be the Weil group of
`π : G →* Γ` and an element `Φ` of infinite order lifting to `G` (for `π₁(U₀) → Gal(k / k₀)` and
the geometric Frobenius, the Weil group of `U₀`), let `s ∈ W` have degree one, and let
`χ : W → A` be a character whose image `χ(Π)` on the geometric part `Π = ker π` is finite. Then
`(W, deg, s)` is a degree datum with degree-zero subgroup `Π`, and the finite part
`ε : w ↦ χ(w) c ^ (-deg w)`, `c = χ(s)`, is a character of finite order with `ε(s) = 1`,
`ε(W) = χ(Π)` and `χ = ε · c ^ deg`.
(blueprint: `cor-wf-rank-one-degree-factorization-curve`) -/
theorem finitePart_ofWeilGroup (hπ : Φ ∈ π.range) (hΦ : ¬IsOfFinOrder Φ) (s : π.weilGroup Φ)
    (hs : π.weilGroupDeg Φ s = Multiplicative.ofAdd 1) (χ : π.weilGroup Φ →* A)
    (hχ : (χ '' (π.kerToWeilGroup Φ).range).Finite) :
    (ofWeilGroup π Φ s hs).deg.ker = (π.kerToWeilGroup Φ).range ∧
      χ = (ofWeilGroup π Φ s hs).finitePart χ * (ofWeilGroup π Φ s hs).degreeCharacter (χ s) ∧
      (ofWeilGroup π Φ s hs).finitePart χ s = 1 ∧
      Set.range ((ofWeilGroup π Φ s hs).finitePart χ) = χ '' (π.kerToWeilGroup Φ).range ∧
      IsOfFinOrder ((ofWeilGroup π Φ s hs).finitePart χ) := by
  set D := ofWeilGroup π Φ s hs
  have hker : D.deg.ker = (π.kerToWeilGroup Φ).range :=
    (π.exact_weilGroupDeg Φ hπ hΦ).2.2.1.symm
  have hrange : Set.range (D.finitePart χ) = χ '' (π.kerToWeilGroup Φ).range := by
    rw [D.range_finitePart, hker]
  exact ⟨hker, D.eq_finitePart_mul_degreeCharacter χ, D.finitePart_degreeOneElement χ, hrange,
    MonoidHom.isOfFinOrder_of_finite_range (hrange ▸ hχ)⟩

end WeilGroup

end DegreeDatum

namespace RepresentedDegreeDatum

open SemidirectProduct

variable {W : Type*} [Group W] {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]
  (D : RepresentedDegreeDatum W n k)

/-- For a representation of rank at most one, conjugation by the Frobenius is trivial on the
geometric monodromy group, so the arithmetic monodromy extension is a direct product. -/
theorem frobeniusAction_eq_one [Subsingleton n] : D.frobeniusAction = 1 := by
  have h : D.frobeniusConj = 1 := by
    ext h : 2
    rw [coe_frobeniusConj_apply, mul_comm_of_subsingleton D.frobenius, mul_inv_cancel_right]
    rfl
  refine MonoidHom.ext_mint ?_
  rw [frobeniusAction, zpowersHom_apply, h, one_zpow, MonoidHom.one_apply]

/-- The image `ρ(u γᵐ)` of an element of degree `m` is the image under `j` of `(ρ(u), m)`. -/
theorem arithmeticMonodromyExtensionHom_rep {u : W} (hu : u ∈ D.degreeZero) (m : ℤ) :
    D.arithmeticMonodromyExtensionHom
        (inl ⟨D.rep u, D.rep_mem_zeroLocus_geometricMonodromy hu⟩ *
          inr (Multiplicative.ofAdd m)) =
      D.rep (u * D.degreeOneElement ^ m) := by
  rw [arithmeticMonodromyExtensionHom_inl_mul_inr, map_mul, map_zpow]
  rfl

/-- For a representation whose geometric image `A = ρ(P)` is finite, the geometric monodromy
group is `H = A`: finite subgroups of `GL n k` are Zariski closed. -/
theorem zeroLocus_geometricMonodromy_eq_of_finite [Finite (D.degreeZero.map D.rep)] :
    zeroLocus D.geometricMonodromy k = D.degreeZero.map D.rep :=
  zeroLocus_vanishingIdeal_eq_of_finite _

/-- **Arithmetic monodromy after finite geometric image.** Let `ρ = χ` be a rank-one
representation whose geometric image `A = χ(P)` is finite. Then the geometric monodromy group is
`H = A` and conjugation by the Frobenius is trivial on it, so that the arithmetic monodromy
extension is `G_arith(χ) = A × ℤ`, by `(h, m) ↦ (h, m)`.
(blueprint: `lem-wf-rank-one-algebraic-extension`) -/
noncomputable def arithmeticMonodromyExtensionEquivProd [Subsingleton n]
    [Finite (D.degreeZero.map D.rep)] :
    D.ArithmeticMonodromyExtension ≃* D.degreeZero.map D.rep × Multiplicative ℤ :=
  (congr (φ₂ := 1) (MulEquiv.subgroupCongr D.zeroLocus_geometricMonodromy_eq_of_finite)
    (MulEquiv.refl _) fun m ↦ by
      ext h : 2
      simp [D.frobeniusAction_eq_one]).trans mulEquivProd

/-- Through `G_arith(χ) = A × ℤ`, the map to matrices is `j(a, m) = a cᵐ`, where `c = χ(γ)` is
the Frobenius. (blueprint: `lem-wf-rank-one-algebraic-extension`) -/
theorem arithmeticMonodromyExtensionHom_arithmeticMonodromyExtensionEquivProd_symm
    [Subsingleton n] [Finite (D.degreeZero.map D.rep)] (a : D.degreeZero.map D.rep) (m : ℤ) :
    D.arithmeticMonodromyExtensionHom
        (D.arithmeticMonodromyExtensionEquivProd.symm (a, Multiplicative.ofAdd m)) =
      a * D.frobenius ^ m := by
  rw [← inl_left_mul_inr_right (D.arithmeticMonodromyExtensionEquivProd.symm _),
    arithmeticMonodromyExtensionHom_inl_mul_inr]
  rfl

/-- Through `G_arith(χ) = A × ℤ`, `j(χ(u), m) = χ(u γᵐ)` for `u ∈ P`.
(blueprint: `lem-wf-rank-one-algebraic-extension`) -/
theorem arithmeticMonodromyExtensionHom_arithmeticMonodromyExtensionEquivProd_symm_rep
    [Subsingleton n] [Finite (D.degreeZero.map D.rep)] {u : W} (hu : u ∈ D.degreeZero) (m : ℤ) :
    D.arithmeticMonodromyExtensionHom
        (D.arithmeticMonodromyExtensionEquivProd.symm
          (⟨D.rep u, Subgroup.mem_map_of_mem _ hu⟩, Multiplicative.ofAdd m)) =
      D.rep (u * D.degreeOneElement ^ m) := by
  rw [arithmeticMonodromyExtensionHom_arithmeticMonodromyExtensionEquivProd_symm, map_mul,
    map_zpow]
  rfl

end RepresentedDegreeDatum

end AlgebraicGeometry.Monodromy
