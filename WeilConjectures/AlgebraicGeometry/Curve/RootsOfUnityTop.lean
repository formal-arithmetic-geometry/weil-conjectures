/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
public import WeilConjectures.AlgebraicGeometry.Curve.Kummer
public import WeilConjectures.AlgebraicGeometry.Curve.Picard
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The top cohomology of `μ_m` on a smooth proper curve

Let `X` be a smooth proper connected curve over an algebraically closed field `k` and `m` an
integer prime to the characteristic. The Kummer sequence identifies `H²(X, μ_m)` with
`Pic(X)/m`, and the degree identifies `Pic(X)/m` with `ℤ/m`, since `Pic⁰(X)` is the group of
points of the Jacobian, a divisible group. In particular `H²(X, μ_m)` has exactly `m` elements
(`AlgebraicGeometry.Scheme.card_sheafH_two_rootsOfUnitySheaf`).

## Main statements

- `AlgebraicGeometry.Scheme.surjective_pow_picardZero`: `Pic⁰(X)` is divisible.
- `AlgebraicGeometry.Scheme.card_sheafH_two_rootsOfUnitySheaf`: `#H²(X, μ_m) = m`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- `Pic⁰` of a smooth proper connected curve over an algebraically closed field is divisible: it
is the group of points of the Jacobian, an abelian variety. -/
lemma surjective_pow_picardZero [GeometricallyIntegral (X ↘ Spec (.of k))] (n : ℕ)
    (hn : 0 < n) : Function.Surjective fun L : picardZero k X ↦ L ^ n := by
  obtain ⟨J, _, -, hP, hS, hG, -, ⟨φ⟩⟩ := exists_jacobian (k := k) (X := X)
  have : Smooth J.hom := SmoothOfRelativeDimension.smooth (arithmeticGenus k X) _
  have : IrreducibleSpace J.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := J.hom)
  have : IsAbelianVariety J := ⟨⟩
  obtain ⟨-, -, hdiv, -, -⟩ := abelianVariety_estimate_of_isAlgClosed (ringChar k) J
  intro L
  obtain ⟨a, ha⟩ := hdiv n hn (φ L)
  exact ⟨φ.symm a, by simp only [← map_pow, ha, MulEquiv.symm_apply_apply]⟩

/-- The degree modulo `m` of the class of an invertible module. -/
noncomputable def picDegreeMod (m : ℕ) : Additive X.Pic →+ ZMod m where
  toFun L := ((picDegreeHom k X L.toMul).toAdd : ZMod m)
  map_zero' := by simp
  map_add' L L' := by simp

lemma ker_picDegreeMod [GeometricallyIntegral (X ↘ Spec (.of k))] [Nonempty X] (m : ℕ)
    (hm : 0 < m) :
    (picDegreeMod (k := k) (X := X) m).ker =
      (zsmulAddGroupHom (α := Additive X.Pic) (m : ℤ)).range := by
  ext L
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
  constructor
  · intro hL
    change (((picDegreeHom k X L.toMul).toAdd : ℤ) : ZMod m) = 0 at hL
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hL
    obtain ⟨d, hd⟩ := hL
    obtain ⟨L₁, hL₁⟩ := surjective_picDegreeHom (k := k) (C := X) (.ofAdd d)
    have h₀ : L.toMul * (L₁ ^ m)⁻¹ ∈ picardZero k X := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hL₁, ← ofAdd_toAdd (picDegreeHom k X _),
        hd, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add, ofAdd_eq_one, nsmul_eq_mul]
      push_cast
      ring
    obtain ⟨L₂, hL₂⟩ := surjective_pow_picardZero (k := k) (X := X) m hm ⟨_, h₀⟩
    refine ⟨Additive.ofMul (L₁ * L₂.1), ?_⟩
    apply Additive.toMul.injective
    rw [zsmulAddGroupHom_apply, natCast_zsmul, toMul_nsmul, toMul_ofMul, mul_pow]
    have := congrArg Subtype.val hL₂
    simp only [SubgroupClass.coe_pow] at this
    rw [this, mul_comm, inv_mul_cancel_right]
  · rintro ⟨L', rfl⟩
    change (((picDegreeHom k X (((m : ℤ) • L').toMul)).toAdd : ℤ) : ZMod m) = 0
    rw [toMul_zsmul, map_zpow, toAdd_zpow, smul_eq_mul, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, zero_mul]

/-- `H²(X, μ_m)` has exactly `m` elements for a smooth proper connected curve `X` over an
algebraically closed field and `m` prime to the characteristic: by the Kummer sequence it is
`Pic(X)/m`, which the degree identifies with `ℤ/m` since `Pic⁰(X)` is divisible. -/
theorem card_sheafH_two_rootsOfUnitySheaf [GeometricallyIntegral (X ↘ Spec (.of k))]
    [Nonempty X] (m : ℕ) [NeZero m] (hm : (m : k) ≠ 0) :
    Nonempty (Sheaf.H (X.rootsOfUnitySheaf m) 2 ≃+ ZMod m) := by
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsCurve (X ↘ Spec (.of k)) :=
    { krullDim_le_one := topologicalKrullDim_le_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) 1 }
  obtain ⟨e₁⟩ :=
    IsCurve.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two_of_smooth (X ↘ Spec (.of k)) m hm
  obtain ⟨e₂⟩ := X.nonempty_addEquiv_cohomologicalPicardGroup
  have hsurj : Function.Surjective (picDegreeMod (k := k) (X := X) m) := fun a ↦ by
    obtain ⟨L, hL⟩ := surjective_picDegreeHom (k := k) (C := X) (.ofAdd (a.val : ℤ))
    refine ⟨Additive.ofMul L, ?_⟩
    change (((picDegreeHom k X L).toAdd : ℤ) : ZMod m) = a
    rw [hL, toAdd_ofAdd, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  let e₃ := QuotientAddGroup.quotientKerEquivOfSurjective _ hsurj
  refine ⟨e₁.trans ((QuotientAddGroup.congr _ _ e₂.symm ?_).trans
    ((QuotientAddGroup.quotientAddEquivOfEq (ker_picDegreeMod m hm0).symm).trans e₃))⟩
  ext L
  simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range, zsmulAddGroupHom_apply]
  constructor
  · rintro ⟨_, ⟨L', rfl⟩, rfl⟩
    exact ⟨e₂.symm L', by rw [map_zsmul]⟩
  · rintro ⟨L', rfl⟩
    exact ⟨_, ⟨e₂ L', rfl⟩, by rw [map_zsmul, AddEquiv.symm_apply_apply]⟩

end AlgebraicGeometry.Scheme
